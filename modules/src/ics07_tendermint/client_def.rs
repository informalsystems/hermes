use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use crate::ics02_client::client_consensus::AnyConsensusState;
use crate::ics02_client::client_def::ClientDef;
use crate::ics02_client::error::Kind;
use crate::ics02_client::client_state::AnyClientState;
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::client_type::ClientType;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::packet::Sequence;
use crate::ics07_tendermint::client_state::ClientState;
use crate::ics07_tendermint::consensus_state::ConsensusState;
use crate::ics07_tendermint::header::Header;
use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes, CommitmentRoot};
use crate::ics24_host::identifier::ConnectionId;
use crate::ics24_host::identifier::{ChannelId, ClientId, PortId};
use crate::Height;

use crate::downcast;


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TendermintClient;

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
    ) -> Result<(Self::ClientState, Self::ConsensusState), Box<dyn std::error::Error>> {
        if client_state.latest_height() >= header.height() {
            return Err(
                format!("received header height ({:?}) is lower than (or equal to) client latest height ({:?})",
                    header.height(), client_state.latest_height).into(),
            );
        }

        if !client_state.frozen_height.is_zero(){
            return Err(
                format!("client is frozen at height ({:?})",
                client_state.frozen_height).into(),
            );
        }

        match ctx.consensus_state(&client_id, header.height()){
            //could the header height be zero ? 
            Some(cs) => { 
                let consensus_state = downcast!(
                    cs => AnyConsensusState::Tendermint
                ).ok_or_else(|| Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?;

                if consensus_state != ConsensusState::from(header.clone()){ 
                    //freeze the client and return the installed consensus state 
                    return Ok((client_state.with_set_frozen(header.height()),
                                consensus_state))
                }
            }
            None =>{}
        }

        let _trusted_consensus_state = 
            match ctx.consensus_state(&client_id, header.trusted_height) {
                Some(ts) => {
                        downcast!(
                            ts => AnyConsensusState::Tendermint
                        ).ok_or_else(|| Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?
                    }
                None => {
                        return Err(
                                format!("Missing consensus state for the client {} at trusted height {:?}",
                                client_id,
                                header.trusted_height).into(),
                            )
                        }
            };



        // TODO: Additional verifications should be implemented here.

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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
    ) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }

    fn verify_upgrade_and_update_state(
        &self,
        _client_state: &Self::ClientState,
        _consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: MerkleProof,
        _proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Box<dyn std::error::Error>> {
        todo!()
    }
}
