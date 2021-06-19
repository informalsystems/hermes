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
use crate::ics07_tendermint::predicates::Predicates;

use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes, CommitmentRoot};
use crate::ics24_host::identifier::ConnectionId;
use crate::ics24_host::identifier::{ChannelId, ClientId, PortId};
use crate::Height;
use std::ops::Sub;
use tendermint::validator::Set;
use tendermint::trust_threshold::TrustThresholdFraction;
//use tendermint::Time;

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
        



        // DONE in HANDLER 
        // if !client_state.frozen_height.is_zero(){
        //     return Err(
        //         format!("client is frozen at height ({:?})",
        //         client_state.frozen_height).into(),
        //     );
        // }

        // // check that the client did not expired  
        // if Time::now().sub(client_state.trusting_period) >= latest_consensus_state.timestamp  { 
        //     return Err(
        //         format!("consensus state expired; it's outside of the trusting period {:?}, {:?}",
        //             latest_consensus_state.timestamp,
        //             Time::now()).into(),
        //     );
        // };


        if client_state.latest_height() >= header.height() {
            return Err(Kind::LowUpdateHeight(
                    header.height(), client_state.latest_height).into(),
            );
        }

        if header.height().is_zero() {
            return Err(Kind::InvalidHeaderHeight(header.height()).into());
        }


        // check if a consensus state is already installed; if so it should 
        // match the untrusted header. 
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

        let latest_consensus_state = match ctx.consensus_state(&client_id, client_state.latest_height){
            //could the header height be zero ? 
            Some(cs) => { 
                downcast!(
                    cs => AnyConsensusState::Tendermint
                ).ok_or_else(|| Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?
                }
            None =>{
                return Err(
                    Kind::ConsensusStateNotFound(client_id.clone(),
                        client_state.latest_height).into(),
                );
            }
        };


        // check that the header is not outside the trusting period 
        if header.signed_header.header().time.sub(client_state.trusting_period) >= latest_consensus_state.timestamp  { 
            return Err(Kind::LowUpdateTimestamp(
                            header.signed_header.header().time.to_rfc3339(), 
                            latest_consensus_state.timestamp.to_rfc3339())
                .into(),
            );
        };

        //ALREADY CHECKED
        // // check monotonicity of height and timestamp 
        // if client_state.latest_height >= header.height() {
        //     return Err(
        //         format!("non monotonic height update {}, {:?}",
        //             client_state.latest_height,
        //             header.height()).into(),
        //     );
        // };

        // check monotonicity of header height vs trusted height.
        // unclear needed  
        if header.trusted_height >= header.height() {
            return Err(
                format!("non monotonic height update w.r.t trusted header {}, {:?}",
                    header.trusted_height,
                    header.height()).into(),
            );
        };

        // check that the versions of the client state and the header match
        if client_state.latest_height.revision_number != header.height().revision_number {
            return Err(Kind::MismatchedRevisions(
                    client_state.latest_height.revision_number,
                    header.height().revision_number).into(),
            );
        };

        if latest_consensus_state.timestamp >= header.signed_header.header().time {
            return Err(Kind:: HeaderTimestampOutsideTrustingTime(
                header.signed_header.header().time.to_rfc3339(), 
                latest_consensus_state.timestamp.to_rfc3339())
            .into(),
            );
        };


       

        let trusted_consensus_state = 
            match ctx.consensus_state(&client_id, header.trusted_height) {
                Some(ts) => {
                        downcast!(
                            ts => AnyConsensusState::Tendermint
                        ).ok_or_else(|| Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?
                    }
                None => {
                        return Err(Kind::ConsensusStateNotFound(
                                client_id,
                                header.trusted_height).into(),
                            )
                        }
            };
        


        if header.height() == header.trusted_height.increment() {
            //adjacent 

            // check that the header's trusted validator set is 
            // the next_validator_set of the trusted consensus state 
            if Set::hash(&header.validator_set) != trusted_consensus_state.next_validators_hash {
                return Err(Kind::InvalidValidatorSet(
                            trusted_consensus_state.next_validators_hash, 
                            Set::hash(&header.validator_set)
                    ).into(),
                )
            }
            let pred = Predicates::default();

            // check that the validators that sign the commit of the untrusted header  
            // have 2/3 of the voting power of the current validator set. 
            match pred.voting_power_in(&header.signed_header,&header.validator_set,TrustThresholdFraction::TWO_THIRDS){
                Err(e) => { return Err(Kind::InsufficientVotingPower(e.to_string()).into());  }
                _ =>{}
            };
            
            

        }else{
            //Non-adjacent 
            let pred = Predicates::default();

            //check that a subset of the trusted validator set, having 1/3 of the voting power
            //signes the commit of the untrusted header 
            match pred.voting_power_in(&header.signed_header,&header.trusted_validator_set,TrustThresholdFraction::default()){
                    Err(e) => { return Err(Kind::NotEnoughTrustedValsSigned(e.to_string()).into());}
                    _ => {}
                };

            // check that the validators that sign the commit of the untrusted header  
            // have 2/3 of the voting power of the current validator set. 
            match pred.voting_power_in(&header.signed_header,&header.validator_set,TrustThresholdFraction::TWO_THIRDS){
                Err(e) => { return Err(Kind::InsufficientVotingPower(e.to_string()).into()); }
                _ =>{}
            };
        }

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
