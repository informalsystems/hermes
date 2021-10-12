use std::convert::TryInto;

use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use tendermint::Time;
use tendermint_light_client::components::verifier::{ProdVerifier, Verdict, Verifier};
use tendermint_light_client::types::{TrustedBlockState, UntrustedBlockState};

use crate::ics02_client::client_consensus::AnyConsensusState;
use crate::ics02_client::client_def::ClientDef;
use crate::ics02_client::client_state::AnyClientState;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::error::Error as Ics02Error;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::packet::Sequence;
use crate::ics07_tendermint::client_state::ClientState;
use crate::ics07_tendermint::consensus_state::ConsensusState;
use crate::ics07_tendermint::error::Error;
use crate::ics07_tendermint::header::Header;

use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes, CommitmentRoot};
use crate::ics24_host::identifier::ConnectionId;
use crate::ics24_host::identifier::{ChannelId, ClientId, PortId};
use crate::prelude::*;
use crate::Height;

use crate::downcast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TendermintClient {
    verifier: ProdVerifier,
}

impl Default for TendermintClient {
    fn default() -> Self {
        Self {
            verifier: ProdVerifier::default(),
        }
    }
}

impl ClientDef for TendermintClient {
    type Header = Header;
    type ClientState = ClientState;
    type ConsensusState = ConsensusState;

    fn check_header_and_update_state(
        &self,
        ctx: &dyn ClientReader,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Ics02Error> {
        if header.height().revision_number != client_state.chain_id.version() {
            return Err(Ics02Error::tendermint_handler_error(
                Error::mismatched_revisions(
                    client_state.chain_id.version(),
                    header.height().revision_number,
                ),
            ));
        }

        // Check if a consensus state is already installed; if so it should
        // match the untrusted header.
        let header_consensus_state = ConsensusState::from(header.clone());
        let existing_consensus_state =
            match ctx.maybe_consensus_state(&client_id, header.height())? {
                Some(cs) => {
                    let cs = downcast_consensus_state(cs)?;
                    // If this consensus state matches, skip verification
                    // (optimization)
                    if cs == header_consensus_state {
                        // Header is already installed and matches the incoming
                        // header (already verified)
                        return Ok((client_state, cs));
                    }
                    Some(cs)
                }
                None => None,
            };

        let trusted_consensus_state =
            downcast_consensus_state(ctx.consensus_state(&client_id, header.trusted_height)?)?;

        let trusted_state = TrustedBlockState {
            header_time: trusted_consensus_state.timestamp,
            height: header
                .trusted_height
                .revision_height
                .try_into()
                .map_err(|_| {
                    Ics02Error::tendermint_handler_error(Error::invalid_header_height(
                        header.trusted_height,
                    ))
                })?,
            next_validators: &header.trusted_validator_set,
            next_validators_hash: trusted_consensus_state.next_validators_hash,
        };

        let untrusted_state = UntrustedBlockState {
            signed_header: &header.signed_header,
            validators: &header.validator_set,
            // NB: This will skip the
            // VerificationPredicates::next_validators_match check for the
            // untrusted state.
            next_validators: None,
        };

        let options = client_state.as_light_client_options()?;

        match self
            .verifier
            .verify(untrusted_state, trusted_state, &options, Time::now())
        {
            Verdict::Success => {}
            Verdict::NotEnoughTrust(voting_power_tally) => {
                return Err(Error::not_enough_trusted_vals_signed(format!(
                    "voting power tally: {}",
                    voting_power_tally
                ))
                .into())
            }
            Verdict::Invalid(detail) => {
                return Err(Ics02Error::tendermint_handler_error(
                    Error::verification_error(detail),
                ))
            }
        }

        // If the header has verified, but its corresponding consensus state
        // differs from the existing consensus state for that height, freeze the
        // client and return the installed consensus state.
        if let Some(cs) = existing_consensus_state {
            if cs != header_consensus_state {
                return Ok((client_state.with_set_frozen(header.height()), cs));
            }
        }

        // Monotonicity checks for timestamps for in-the-middle updates
        // (cs-new, cs-next, cs-latest)
        if header.height() < client_state.latest_height() {
            let maybe_next_cs = ctx
                .next_consensus_state(&client_id, header.height())?
                .map(downcast_consensus_state)
                .transpose()?;

            if let Some(next_cs) = maybe_next_cs {
                // New (untrusted) header timestamp cannot occur after next
                // consensus state's height
                if header.signed_header.header().time > next_cs.timestamp {
                    return Err(Ics02Error::tendermint_handler_error(
                        Error::header_timestamp_too_high(
                            header.signed_header.header().time.to_string(),
                            next_cs.timestamp.to_string(),
                        ),
                    ));
                }
            }
        }
        // (cs-trusted, cs-prev, cs-new)
        if header.trusted_height < header.height() {
            let maybe_prev_cs = ctx
                .prev_consensus_state(&client_id, header.height())?
                .map(downcast_consensus_state)
                .transpose()?;

            if let Some(prev_cs) = maybe_prev_cs {
                // New (untrusted) header timestamp cannot occur before the
                // previous consensus state's height
                if header.signed_header.header().time < prev_cs.timestamp {
                    return Err(Ics02Error::tendermint_handler_error(
                        Error::header_timestamp_too_low(
                            header.signed_header.header().time.to_string(),
                            prev_cs.timestamp.to_string(),
                        ),
                    ));
                }
            }
        }

        Ok((
            client_state.with_header(header.clone()),
            ConsensusState::from(header),
        ))
    }

    fn verify_client_consensus_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _client_id: &ClientId,
        _consensus_height: Height,
        _expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_connection_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _connection_id: Option<&ConnectionId>,
        _expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_channel_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _expected_channel_end: &ChannelEnd,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_client_full_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _root: &CommitmentRoot,
        _prefix: &CommitmentPrefix,
        _client_id: &ClientId,
        _proof: &CommitmentProofBytes,
        _expected_client_state: &AnyClientState,
    ) -> Result<(), Ics02Error> {
        unimplemented!()
    }

    fn verify_packet_data(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _proof: &CommitmentProofBytes,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _seq: &Sequence,
        _data: String,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_packet_acknowledgement(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _proof: &CommitmentProofBytes,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _seq: &Sequence,
        _data: Vec<u8>,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_next_sequence_recv(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _proof: &CommitmentProofBytes,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _seq: &Sequence,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_packet_receipt_absence(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _proof: &CommitmentProofBytes,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _seq: &Sequence,
    ) -> Result<(), Ics02Error> {
        todo!()
    }

    fn verify_upgrade_and_update_state(
        &self,
        _client_state: &Self::ClientState,
        _consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: MerkleProof,
        _proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Ics02Error> {
        todo!()
    }
}

fn downcast_consensus_state(cs: AnyConsensusState) -> Result<ConsensusState, Ics02Error> {
    downcast!(
        cs => AnyConsensusState::Tendermint
    )
    .ok_or_else(|| Ics02Error::client_args_type_mismatch(ClientType::Tendermint))
}
