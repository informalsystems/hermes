use crate::core::ics02_client::context::ClientReader;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics23_commitment::merkle::{apply_prefix, MerkleProof};
use crate::core::ics24_host::path::{
    AcksPath, ChannelEndsPath, ClientConsensusStatePath, ClientStatePath, CommitmentsPath,
    ConnectionsPath, ReceiptsPath, SeqRecvsPath,
};
use crate::core::ics24_host::Path;
use crate::prelude::*;

use core::convert::{TryFrom, TryInto};
use core::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::Height as RawHeight;
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
use ibc_proto::ibc::lightclients::tendermint::v1::ClientState as RawTmClientState;
use ibc_proto::protobuf::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};
use tendermint_light_client_verifier::options::Options;
use tendermint_light_client_verifier::types::{TrustedBlockState, UntrustedBlockState};
use tendermint_light_client_verifier::{ProdVerifier, Verdict, Verifier};

use crate::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use crate::clients::ics07_tendermint::error::Error;
use crate::clients::ics07_tendermint::header::Header as TmHeader;
use crate::core::ics02_client::client_state::{
    ClientState as Ics2ClientState, UpdatedState, UpgradeOptions as CoreUpgradeOptions,
};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState;
use crate::core::ics02_client::error::{Error as Ics02Error, ErrorDetail as Ics02ErrorDetail};
use crate::core::ics02_client::trust_threshold::TrustThreshold;
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics23_commitment::specs::ProofSpecs;
use crate::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use crate::timestamp::{Timestamp, ZERO_DURATION};
use crate::Height;

pub const TENDERMINT_CLIENT_STATE_TYPE_URL: &str = "/ibc.lightclients.tendermint.v1.ClientState";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClientState {
    pub chain_id: ChainId,
    pub trust_level: TrustThreshold,
    pub trusting_period: Duration,
    pub unbonding_period: Duration,
    pub max_clock_drift: Duration,
    pub latest_height: Height,
    pub proof_specs: ProofSpecs,
    pub upgrade_path: Vec<String>,
    pub allow_update: AllowUpdate,
    pub frozen_height: Option<Height>,
    #[serde(skip)]
    pub verifier: ProdVerifier,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AllowUpdate {
    pub after_expiry: bool,
    pub after_misbehaviour: bool,
}

impl ClientState {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        chain_id: ChainId,
        trust_level: TrustThreshold,
        trusting_period: Duration,
        unbonding_period: Duration,
        max_clock_drift: Duration,
        latest_height: Height,
        proof_specs: ProofSpecs,
        upgrade_path: Vec<String>,
        allow_update: AllowUpdate,
    ) -> Result<ClientState, Error> {
        // Basic validation of trusting period and unbonding period: each should be non-zero.
        if trusting_period <= Duration::new(0, 0) {
            return Err(Error::invalid_trusting_period(format!(
                "ClientState trusting period ({:?}) must be greater than zero",
                trusting_period
            )));
        }

        if unbonding_period <= Duration::new(0, 0) {
            return Err(Error::invalid_unbonding_period(format!(
                "ClientState unbonding period ({:?}) must be greater than zero",
                unbonding_period
            )));
        }

        if trusting_period >= unbonding_period {
            return Err(Error::invalid_trusting_period(format!(
                "ClientState trusting period ({:?}) must be smaller than unbonding period ({:?})",
                trusting_period, unbonding_period,
            )));
        }

        // `TrustThreshold` is guaranteed to be in the range `[0, 1)`, but a `TrustThreshold::ZERO`
        // value is invalid in this context
        if trust_level == TrustThreshold::ZERO {
            return Err(Error::validation(
                "ClientState trust-level cannot be zero".to_string(),
            ));
        }

        // Disallow empty proof-specs
        if proof_specs.is_empty() {
            return Err(Error::validation(
                "ClientState proof-specs cannot be empty".to_string(),
            ));
        }

        Ok(Self {
            chain_id,
            trust_level,
            trusting_period,
            unbonding_period,
            max_clock_drift,
            latest_height,
            proof_specs,
            upgrade_path,
            allow_update,
            frozen_height: None,
            verifier: ProdVerifier::default(),
        })
    }

    pub fn latest_height(&self) -> Height {
        self.latest_height
    }

    pub fn with_header(self, h: TmHeader) -> Result<Self, Error> {
        Ok(ClientState {
            latest_height: Height::new(
                self.latest_height.revision_number(),
                h.signed_header.header.height.into(),
            )
            .map_err(|_| Error::invalid_header_height(h.signed_header.header.height.value()))?,
            ..self
        })
    }

    pub fn with_frozen_height(self, h: Height) -> Result<Self, Error> {
        Ok(Self {
            frozen_height: Some(h),
            ..self
        })
    }

    /// Get the refresh time to ensure the state does not expire
    pub fn refresh_time(&self) -> Option<Duration> {
        Some(2 * self.trusting_period / 3)
    }

    /// Helper method to produce a [`Options`] struct for use in
    /// Tendermint-specific light client verification.
    pub fn as_light_client_options(&self) -> Result<Options, Error> {
        Ok(Options {
            trust_threshold: self
                .trust_level
                .try_into()
                .map_err(|e: Ics02Error| Error::invalid_trust_threshold(e.to_string()))?,
            trusting_period: self.trusting_period,
            clock_drift: self.max_clock_drift,
        })
    }

    /// Verify the time and height delays
    pub fn verify_delay_passed(
        current_time: Timestamp,
        current_height: Height,
        processed_time: Timestamp,
        processed_height: Height,
        delay_period_time: Duration,
        delay_period_blocks: u64,
    ) -> Result<(), Error> {
        let earliest_time =
            (processed_time + delay_period_time).map_err(Error::timestamp_overflow)?;
        if !(current_time == earliest_time || current_time.after(&earliest_time)) {
            return Err(Error::not_enough_time_elapsed(current_time, earliest_time));
        }

        let earliest_height = processed_height.add(delay_period_blocks);
        if current_height < earliest_height {
            return Err(Error::not_enough_blocks_elapsed(
                current_height,
                earliest_height,
            ));
        }

        Ok(())
    }

    /// Verify that the client is at a sufficient height and unfrozen at the given height
    pub fn verify_height(&self, height: Height) -> Result<(), Error> {
        if self.latest_height < height {
            return Err(Error::insufficient_height(self.latest_height(), height));
        }

        match self.frozen_height {
            Some(frozen_height) if frozen_height <= height => {
                Err(Error::client_frozen(frozen_height, height))
            }
            _ => Ok(()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UpgradeOptions {
    pub unbonding_period: Duration,
}

impl CoreUpgradeOptions for UpgradeOptions {}

impl Ics2ClientState for ClientState {
    fn chain_id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn latest_height(&self) -> Height {
        self.latest_height
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height
    }

    fn upgrade(
        &mut self,
        upgrade_height: Height,
        upgrade_options: &dyn CoreUpgradeOptions,
        chain_id: ChainId,
    ) {
        let upgrade_options = upgrade_options
            .as_any()
            .downcast_ref::<UpgradeOptions>()
            .expect("UpgradeOptions not of type Tendermint");

        // Reset custom fields to zero values
        self.trusting_period = ZERO_DURATION;
        self.trust_level = TrustThreshold::ZERO;
        self.allow_update.after_expiry = false;
        self.allow_update.after_misbehaviour = false;
        self.frozen_height = None;
        self.max_clock_drift = ZERO_DURATION;

        // Upgrade the client state
        self.latest_height = upgrade_height;
        self.unbonding_period = upgrade_options.unbonding_period;
        self.chain_id = chain_id;
    }

    fn expired(&self, elapsed: Duration) -> bool {
        elapsed > self.trusting_period
    }

    fn initialise(&self, consensus_state: Any) -> Result<Box<dyn ConsensusState>, Ics02Error> {
        TmConsensusState::try_from(consensus_state).map(TmConsensusState::into_box)
    }

    fn check_header_and_update_state(
        &self,
        ctx: &dyn ClientReader,
        client_id: ClientId,
        header: Any,
    ) -> Result<UpdatedState, Ics02Error> {
        fn maybe_consensus_state(
            ctx: &dyn ClientReader,
            client_id: &ClientId,
            height: Height,
        ) -> Result<Option<Box<dyn ConsensusState>>, Ics02Error> {
            match ctx.consensus_state(client_id, height) {
                Ok(cs) => Ok(Some(cs)),
                Err(e) => match e.detail() {
                    Ics02ErrorDetail::ConsensusStateNotFound(_) => Ok(None),
                    _ => Err(e),
                },
            }
        }

        let client_state = downcast_tm_client_state(self)?.clone();
        let header = TmHeader::try_from(header)?;

        if header.height().revision_number() != client_state.chain_id().version() {
            return Err(Ics02Error::client_specific(
                Error::mismatched_revisions(
                    client_state.chain_id().version(),
                    header.height().revision_number(),
                )
                .to_string(),
            ));
        }

        // Check if a consensus state is already installed; if so it should
        // match the untrusted header.
        let header_consensus_state = TmConsensusState::from(header.clone());
        let existing_consensus_state =
            match maybe_consensus_state(ctx, &client_id, header.height())? {
                Some(cs) => {
                    let cs = downcast_tm_consensus_state(cs.as_ref())?;
                    // If this consensus state matches, skip verification
                    // (optimization)
                    if cs == header_consensus_state {
                        // Header is already installed and matches the incoming
                        // header (already verified)
                        return Ok(UpdatedState {
                            client_state: client_state.into_box(),
                            consensus_state: cs.into_box(),
                        });
                    }
                    Some(cs)
                }
                None => None,
            };

        let trusted_consensus_state = downcast_tm_consensus_state(
            ctx.consensus_state(&client_id, header.trusted_height)?
                .as_ref(),
        )?;

        let trusted_state = TrustedBlockState {
            header_time: trusted_consensus_state.timestamp,
            height: header
                .trusted_height
                .revision_height()
                .try_into()
                .map_err(|_| {
                    Ics02Error::client_specific(
                        Error::invalid_header_height(header.trusted_height.revision_height())
                            .to_string(),
                    )
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

        let verdict = self.verifier.verify(
            untrusted_state,
            trusted_state,
            &options,
            ctx.host_timestamp().into_tm_time().unwrap(),
        );

        match verdict {
            Verdict::Success => {}
            Verdict::NotEnoughTrust(voting_power_tally) => {
                return Err(Error::not_enough_trusted_vals_signed(format!(
                    "voting power tally: {}",
                    voting_power_tally
                ))
                .into());
            }
            Verdict::Invalid(detail) => return Err(Error::verification_error(detail).into()),
        }

        // If the header has verified, but its corresponding consensus state
        // differs from the existing consensus state for that height, freeze the
        // client and return the installed consensus state.
        if let Some(cs) = existing_consensus_state {
            if cs != header_consensus_state {
                return Ok(UpdatedState {
                    client_state: client_state.with_frozen_height(header.height())?.into_box(),
                    consensus_state: cs.into_box(),
                });
            }
        }

        // Monotonicity checks for timestamps for in-the-middle updates
        // (cs-new, cs-next, cs-latest)
        if header.height() < client_state.latest_height() {
            let maybe_next_cs = ctx
                .next_consensus_state(&client_id, header.height())?
                .as_ref()
                .map(|cs| downcast_tm_consensus_state(cs.as_ref()))
                .transpose()?;

            if let Some(next_cs) = maybe_next_cs {
                // New (untrusted) header timestamp cannot occur after next
                // consensus state's height
                if header.signed_header.header().time > next_cs.timestamp {
                    return Err(Ics02Error::client_specific(
                        Error::header_timestamp_too_high(
                            header.signed_header.header().time.to_string(),
                            next_cs.timestamp.to_string(),
                        )
                        .to_string(),
                    ));
                }
            }
        }

        // (cs-trusted, cs-prev, cs-new)
        if header.trusted_height < header.height() {
            let maybe_prev_cs = ctx
                .prev_consensus_state(&client_id, header.height())?
                .as_ref()
                .map(|cs| downcast_tm_consensus_state(cs.as_ref()))
                .transpose()?;

            if let Some(prev_cs) = maybe_prev_cs {
                // New (untrusted) header timestamp cannot occur before the
                // previous consensus state's height
                if header.signed_header.header().time < prev_cs.timestamp {
                    return Err(Ics02Error::client_specific(
                        Error::header_timestamp_too_low(
                            header.signed_header.header().time.to_string(),
                            prev_cs.timestamp.to_string(),
                        )
                        .to_string(),
                    ));
                }
            }
        }

        Ok(UpdatedState {
            client_state: client_state.with_header(header.clone())?.into_box(),
            consensus_state: TmConsensusState::from(header).into_box(),
        })
    }

    fn verify_upgrade_and_update_state(
        &self,
        _consensus_state: Any,
        _proof_upgrade_client: RawMerkleProof,
        _proof_upgrade_consensus_state: RawMerkleProof,
    ) -> Result<UpdatedState, Ics02Error> {
        unimplemented!()
    }

    fn verify_client_consensus_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;

        let path = ClientConsensusStatePath {
            client_id: client_id.clone(),
            epoch: consensus_height.revision_number(),
            height: consensus_height.revision_height(),
        };
        let value = expected_consensus_state
            .encode_vec()
            .map_err(Ics02Error::invalid_any_consensus_state)?;

        verify_membership(client_state, prefix, proof, root, path, value)
    }

    fn verify_connection_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;

        let path = ConnectionsPath(connection_id.clone());
        let value = expected_connection_end
            .encode_vec()
            .map_err(Ics02Error::invalid_connection_end)?;
        verify_membership(client_state, prefix, proof, root, path, value)
    }

    fn verify_channel_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &crate::core::ics04_channel::channel::ChannelEnd,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;

        let path = ChannelEndsPath(port_id.clone(), channel_id.clone());
        let value = expected_channel_end
            .encode_vec()
            .map_err(Ics02Error::invalid_channel_end)?;
        verify_membership(client_state, prefix, proof, root, path, value)
    }

    fn verify_client_full_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: Any,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;

        let path = ClientStatePath(client_id.clone());
        let value = expected_client_state.encode_to_vec();
        verify_membership(client_state, prefix, proof, root, path, value)
    }

    fn verify_packet_data(
        &self,
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let commitment_path = CommitmentsPath {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
        };

        verify_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            commitment_path,
            commitment.into_vec(),
        )
    }

    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack_commitment: AcknowledgementCommitment,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let ack_path = AcksPath {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
        };
        verify_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            ack_path,
            ack_commitment.into_vec(),
        )
    }

    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let mut seq_bytes = Vec::new();
        u64::from(sequence)
            .encode(&mut seq_bytes)
            .expect("buffer size too small");

        let seq_path = SeqRecvsPath(port_id.clone(), channel_id.clone());

        verify_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            seq_path,
            seq_bytes,
        )
    }

    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ChannelReader,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Ics02Error> {
        let client_state = downcast_tm_client_state(self)?;
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let receipt_path = ReceiptsPath {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
        };
        verify_non_membership(
            client_state,
            connection_end.counterparty().prefix(),
            proof,
            root,
            receipt_path,
        )
    }
}

fn verify_membership(
    client_state: &ClientState,
    prefix: &CommitmentPrefix,
    proof: &CommitmentProofBytes,
    root: &CommitmentRoot,
    path: impl Into<Path>,
    value: Vec<u8>,
) -> Result<(), Ics02Error> {
    let merkle_path = apply_prefix(prefix, vec![path.into().to_string()]);
    let merkle_proof: MerkleProof = RawMerkleProof::try_from(proof.clone())
        .map_err(Ics02Error::invalid_commitment_proof)?
        .into();

    merkle_proof
        .verify_membership(
            &client_state.proof_specs,
            root.clone().into(),
            merkle_path,
            value,
            0,
        )
        .map_err(Ics02Error::ics23_verification)
}

fn verify_non_membership(
    client_state: &ClientState,
    prefix: &CommitmentPrefix,
    proof: &CommitmentProofBytes,
    root: &CommitmentRoot,
    path: impl Into<Path>,
) -> Result<(), Ics02Error> {
    let merkle_path = apply_prefix(prefix, vec![path.into().to_string()]);
    let merkle_proof: MerkleProof = RawMerkleProof::try_from(proof.clone())
        .map_err(Ics02Error::invalid_commitment_proof)?
        .into();

    merkle_proof
        .verify_non_membership(&client_state.proof_specs, root.clone().into(), merkle_path)
        .map_err(Ics02Error::ics23_verification)
}

fn verify_delay_passed(
    ctx: &dyn ChannelReader,
    height: Height,
    connection_end: &ConnectionEnd,
) -> Result<(), Ics02Error> {
    let current_timestamp = ctx.host_timestamp();
    let current_height = ctx.host_height();

    let client_id = connection_end.client_id();
    let processed_time = ctx
        .client_update_time(client_id, height)
        .map_err(|_| Error::processed_time_not_found(client_id.clone(), height))?;
    let processed_height = ctx
        .client_update_height(client_id, height)
        .map_err(|_| Error::processed_height_not_found(client_id.clone(), height))?;

    let delay_period_time = connection_end.delay_period();
    let delay_period_height = ctx.block_delay(delay_period_time);

    ClientState::verify_delay_passed(
        current_timestamp,
        current_height,
        processed_time,
        processed_height,
        delay_period_time,
        delay_period_height,
    )
    .map_err(|e| e.into())
}
fn downcast_tm_client_state(cs: &dyn Ics2ClientState) -> Result<&ClientState, Ics02Error> {
    cs.as_any()
        .downcast_ref::<ClientState>()
        .ok_or_else(|| Ics02Error::client_args_type_mismatch(ClientType::Tendermint))
}

fn downcast_tm_consensus_state(cs: &dyn ConsensusState) -> Result<TmConsensusState, Ics02Error> {
    cs.as_any()
        .downcast_ref::<TmConsensusState>()
        .ok_or_else(|| Ics02Error::client_args_type_mismatch(ClientType::Tendermint))
        .map(Clone::clone)
}

impl Protobuf<RawTmClientState> for ClientState {}

impl TryFrom<RawTmClientState> for ClientState {
    type Error = Error;

    fn try_from(raw: RawTmClientState) -> Result<Self, Self::Error> {
        let trust_level = raw
            .trust_level
            .clone()
            .ok_or_else(Error::missing_trusting_period)?;

        // In `RawClientState`, a `frozen_height` of `0` means "not frozen".
        // See:
        // https://github.com/cosmos/ibc-go/blob/8422d0c4c35ef970539466c5bdec1cd27369bab3/modules/light-clients/07-tendermint/types/client_state.go#L74
        let frozen_height = raw
            .frozen_height
            .and_then(|raw_height| raw_height.try_into().ok());

        #[allow(deprecated)]
        Ok(Self {
            chain_id: ChainId::from_string(raw.chain_id.as_str()),
            trust_level: trust_level
                .try_into()
                .map_err(|e| Error::invalid_trust_threshold(format!("{}", e)))?,
            trusting_period: raw
                .trusting_period
                .ok_or_else(Error::missing_trusting_period)?
                .try_into()
                .map_err(|_| Error::negative_trusting_period())?,
            unbonding_period: raw
                .unbonding_period
                .ok_or_else(Error::missing_unbonding_period)?
                .try_into()
                .map_err(|_| Error::negative_unbonding_period())?,
            max_clock_drift: raw
                .max_clock_drift
                .ok_or_else(Error::missing_max_clock_drift)?
                .try_into()
                .map_err(|_| Error::negative_max_clock_drift())?,
            latest_height: raw
                .latest_height
                .ok_or_else(Error::missing_latest_height)?
                .try_into()
                .map_err(|_| Error::missing_latest_height())?,
            frozen_height,
            upgrade_path: raw.upgrade_path,
            allow_update: AllowUpdate {
                after_expiry: raw.allow_update_after_expiry,
                after_misbehaviour: raw.allow_update_after_misbehaviour,
            },
            proof_specs: raw.proof_specs.into(),
            verifier: ProdVerifier::default(),
        })
    }
}

impl From<ClientState> for RawTmClientState {
    fn from(value: ClientState) -> Self {
        #[allow(deprecated)]
        Self {
            chain_id: value.chain_id.to_string(),
            trust_level: Some(value.trust_level.into()),
            trusting_period: Some(value.trusting_period.into()),
            unbonding_period: Some(value.unbonding_period.into()),
            max_clock_drift: Some(value.max_clock_drift.into()),
            frozen_height: Some(value.frozen_height.map(|height| height.into()).unwrap_or(
                RawHeight {
                    revision_number: 0,
                    revision_height: 0,
                },
            )),
            latest_height: Some(value.latest_height.into()),
            proof_specs: value.proof_specs.into(),
            upgrade_path: value.upgrade_path,
            allow_update_after_expiry: value.allow_update.after_expiry,
            allow_update_after_misbehaviour: value.allow_update.after_misbehaviour,
        }
    }
}

impl Protobuf<Any> for ClientState {}

impl TryFrom<Any> for ClientState {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        use bytes::Buf;
        use core::ops::Deref;

        fn decode_client_state<B: Buf>(buf: B) -> Result<ClientState, Error> {
            RawTmClientState::decode(buf)
                .map_err(Error::decode)?
                .try_into()
        }

        match raw.type_url.as_str() {
            TENDERMINT_CLIENT_STATE_TYPE_URL => {
                decode_client_state(raw.value.deref()).map_err(Into::into)
            }
            _ => Err(Ics02Error::unknown_client_state_type(raw.type_url)),
        }
    }
}

impl From<ClientState> for Any {
    fn from(client_state: ClientState) -> Self {
        Any {
            type_url: TENDERMINT_CLIENT_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawTmClientState>::encode_vec(&client_state)
                .expect("encoding to `Any` from `TmClientState`"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    use crate::Height;
    use core::time::Duration;
    use test_log::test;

    use ibc_proto::ics23::ProofSpec as Ics23ProofSpec;
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    use crate::clients::ics07_tendermint::client_state::{AllowUpdate, ClientState};
    use crate::core::ics02_client::trust_threshold::TrustThreshold;
    use crate::core::ics23_commitment::specs::ProofSpecs;
    use crate::core::ics24_host::identifier::ChainId;
    use crate::test::test_serialization_roundtrip;
    use crate::timestamp::{Timestamp, ZERO_DURATION};

    #[derive(Clone, Debug, PartialEq)]
    struct ClientStateParams {
        id: ChainId,
        trust_level: TrustThreshold,
        trusting_period: Duration,
        unbonding_period: Duration,
        max_clock_drift: Duration,
        latest_height: Height,
        proof_specs: ProofSpecs,
        upgrade_path: Vec<String>,
        allow_update: AllowUpdate,
    }

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data =
            include_str!("../../../tests/support/query/serialization/client_state.json");
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data =
            include_str!("../../../tests/support/query/serialization/client_state_proof.json");
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn client_state_new() {
        // Define a "default" set of parameters to reuse throughout these tests.
        let default_params: ClientStateParams = ClientStateParams {
            id: ChainId::default(),
            trust_level: TrustThreshold::ONE_THIRD,
            trusting_period: Duration::new(64000, 0),
            unbonding_period: Duration::new(128000, 0),
            max_clock_drift: Duration::new(3, 0),
            latest_height: Height::new(0, 10).unwrap(),
            proof_specs: ProofSpecs::default(),
            upgrade_path: vec!["".to_string()],
            allow_update: AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        };

        struct Test {
            name: String,
            params: ClientStateParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Valid parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Invalid unbonding period".to_string(),
                params: ClientStateParams {
                    unbonding_period: ZERO_DURATION,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too small) trusting period".to_string(),
                params: ClientStateParams {
                    trusting_period: ZERO_DURATION,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too large) trusting period w.r.t. unbonding period".to_string(),
                params: ClientStateParams {
                    trusting_period: Duration::new(11, 0),
                    unbonding_period: Duration::new(10, 0),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too small) trusting trust threshold".to_string(),
                params: ClientStateParams {
                    trust_level: TrustThreshold::ZERO,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (empty) proof specs".to_string(),
                params: ClientStateParams {
                    proof_specs: ProofSpecs::from(Vec::<Ics23ProofSpec>::new()),
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let cs_result = ClientState::new(
                p.id,
                p.trust_level,
                p.trusting_period,
                p.unbonding_period,
                p.max_clock_drift,
                p.latest_height,
                p.proof_specs,
                p.upgrade_path,
                p.allow_update,
            );

            assert_eq!(
                test.want_pass,
                cs_result.is_ok(),
                "ClientState::new() failed for test {}, \nmsg{:?} with error {:?}",
                test.name,
                test.params.clone(),
                cs_result.err(),
            );
        }
    }

    #[test]
    fn client_state_verify_delay_passed() {
        #[derive(Debug, Clone)]
        struct Params {
            current_time: Timestamp,
            current_height: Height,
            processed_time: Timestamp,
            processed_height: Height,
            delay_period_time: Duration,
            delay_period_blocks: u64,
        }
        struct Test {
            name: String,
            params: Params,
            want_pass: bool,
        }
        let now = Timestamp::now();

        let tests: Vec<Test> = vec![
            Test {
                name: "Successful delay verification".to_string(),
                params: Params {
                    current_time: (now + Duration::from_nanos(2000)).unwrap(),
                    current_height: Height::new(0, 5).unwrap(),
                    processed_time: (now + Duration::from_nanos(1000)).unwrap(),
                    processed_height: Height::new(0, 3).unwrap(),
                    delay_period_time: Duration::from_nanos(500),
                    delay_period_blocks: 2,
                },
                want_pass: true,
            },
            Test {
                name: "Delay period(time) has not elapsed".to_string(),
                params: Params {
                    current_time: (now + Duration::from_nanos(1200)).unwrap(),
                    current_height: Height::new(0, 5).unwrap(),
                    processed_time: (now + Duration::from_nanos(1000)).unwrap(),
                    processed_height: Height::new(0, 3).unwrap(),
                    delay_period_time: Duration::from_nanos(500),
                    delay_period_blocks: 2,
                },
                want_pass: false,
            },
            Test {
                name: "Delay period(blocks) has not elapsed".to_string(),
                params: Params {
                    current_time: (now + Duration::from_nanos(2000)).unwrap(),
                    current_height: Height::new(0, 5).unwrap(),
                    processed_time: (now + Duration::from_nanos(1000)).unwrap(),
                    processed_height: Height::new(0, 4).unwrap(),
                    delay_period_time: Duration::from_nanos(500),
                    delay_period_blocks: 2,
                },
                want_pass: false,
            },
        ];

        for test in tests {
            let res = ClientState::verify_delay_passed(
                test.params.current_time,
                test.params.current_height,
                test.params.processed_time,
                test.params.processed_height,
                test.params.delay_period_time,
                test.params.delay_period_blocks,
            );

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "ClientState::verify_delay_passed() failed for test {}, \nmsg{:?} with error {:?}",
                test.name,
                test.params.clone(),
                res.err(),
            );
        }
    }

    #[test]
    fn client_state_verify_height() {
        // Define a "default" set of parameters to reuse throughout these tests.
        let default_params: ClientStateParams = ClientStateParams {
            id: ChainId::default(),
            trust_level: TrustThreshold::ONE_THIRD,
            trusting_period: Duration::new(64000, 0),
            unbonding_period: Duration::new(128000, 0),
            max_clock_drift: Duration::new(3, 0),
            latest_height: Height::new(1, 10).unwrap(),
            proof_specs: ProofSpecs::default(),
            upgrade_path: vec!["".to_string()],
            allow_update: AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        };

        struct Test {
            name: String,
            height: Height,
            setup: Option<Box<dyn FnOnce(ClientState) -> ClientState>>,
            want_pass: bool,
        }

        let tests = vec![
            Test {
                name: "Successful height verification".to_string(),
                height: Height::new(1, 8).unwrap(),
                setup: None,
                want_pass: true,
            },
            Test {
                name: "Invalid (too large)  client height".to_string(),
                height: Height::new(1, 12).unwrap(),
                setup: None,
                want_pass: false,
            },
            Test {
                name: "Invalid, client is frozen below current height".to_string(),
                height: Height::new(1, 6).unwrap(),
                setup: Some(Box::new(|client_state| {
                    client_state
                        .with_frozen_height(Height::new(1, 5).unwrap())
                        .unwrap()
                })),
                want_pass: false,
            },
        ];

        for test in tests {
            let p = default_params.clone();
            let client_state = ClientState::new(
                p.id,
                p.trust_level,
                p.trusting_period,
                p.unbonding_period,
                p.max_clock_drift,
                p.latest_height,
                p.proof_specs,
                p.upgrade_path,
                p.allow_update,
            )
            .unwrap();
            let client_state = match test.setup {
                Some(setup) => (setup)(client_state),
                _ => client_state,
            };
            let res = client_state.verify_height(test.height);

            assert_eq!(
                test.want_pass,
                res.is_ok(),
                "ClientState::verify_delay_height() failed for test {}, \nmsg{:?} with error {:?}",
                test.name,
                test.height,
                res.err(),
            );
        }
    }
}

#[cfg(any(test, feature = "mocks"))]
pub mod test_util {
    use crate::prelude::*;
    use core::time::Duration;

    use tendermint::block::Header;

    use crate::clients::ics07_tendermint::client_state::{AllowUpdate, ClientState};
    use crate::core::ics02_client::height::Height;
    use crate::core::ics24_host::identifier::ChainId;

    pub fn get_dummy_tendermint_client_state(tm_header: Header) -> ClientState {
        ClientState::new(
            ChainId::from(tm_header.chain_id.clone()),
            Default::default(),
            Duration::from_secs(64000),
            Duration::from_secs(128000),
            Duration::from_millis(3000),
            Height::new(
                ChainId::chain_version(tm_header.chain_id.as_str()),
                u64::from(tm_header.height),
            )
            .unwrap(),
            Default::default(),
            vec!["".to_string()],
            AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        )
        .unwrap()
    }
}
