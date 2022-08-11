use beefy_client::BeefyLightClient;
use beefy_client_primitives::ClientState as LightClientState;
use beefy_client_primitives::{ParachainHeader, ParachainsUpdateProof};
use codec::{Decode, Encode};
use core::fmt::Debug;
use pallet_mmr_primitives::BatchProof;
use sp_core::H256;
use tendermint_proto::Protobuf;

use crate::clients::host_functions::{HostFunctionsManager, HostFunctionsProvider};
use crate::clients::ics11_beefy::client_state::ClientState;
use crate::clients::ics11_beefy::consensus_state::ConsensusState;
use crate::clients::ics11_beefy::error::Error as BeefyError;
use crate::clients::ics11_beefy::header::BeefyHeader;
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_def::{ClientDef, ConsensusUpdateResult};
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::packet::Sequence;

use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};

use crate::core::ics24_host::identifier::ConnectionId;
use crate::core::ics24_host::identifier::{ChannelId, ClientId, PortId};
use crate::core::ics24_host::Path;
use crate::core::ics26_routing::context::ReaderContext;
use crate::prelude::*;
use crate::Height;
use core::marker::PhantomData;

use crate::core::ics24_host::path::{
    AcksPath, ChannelEndsPath, ClientConsensusStatePath, ClientStatePath, CommitmentsPath,
    ConnectionsPath, ReceiptsPath, SeqRecvsPath,
};
use crate::downcast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BeefyClient<HostFunctions>(PhantomData<HostFunctions>);

impl<HostFunctions> Default for BeefyClient<HostFunctions> {
    fn default() -> Self {
        Self(PhantomData::default())
    }
}

impl<HostFunctions: HostFunctionsProvider> ClientDef for BeefyClient<HostFunctions> {
    type Header = BeefyHeader;
    type ClientState = ClientState;
    type ConsensusState = ConsensusState;

    fn verify_header(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error> {
        let light_client_state = LightClientState {
            latest_beefy_height: client_state.latest_beefy_height,
            mmr_root_hash: client_state.mmr_root_hash,
            current_authorities: client_state.authority.clone(),
            next_authorities: client_state.next_authority_set.clone(),
            beefy_activation_block: client_state.beefy_activation_block,
        };
        let mut light_client = BeefyLightClient::<HostFunctionsManager<HostFunctions>>::new();
        // If mmr update exists verify it and return the new light client state
        // or else return existing light client state
        let light_client_state = if let Some(mmr_update) = header.mmr_update_proof {
            light_client
                .verify_mmr_root_with_proof(light_client_state, mmr_update)
                .map_err(|e| Error::beefy(BeefyError::invalid_mmr_update(format!("{:?}", e))))?
        } else {
            light_client_state
        };

        // Extract parachain headers from the beefy header if they exist
        let mut leaf_indices = vec![];
        let parachain_headers = header
            .parachain_headers
            .clone()
            .into_iter()
            .map(|header| {
                let leaf_index = client_state
                    .to_leaf_index(header.partial_mmr_leaf.parent_number_and_hash.0 + 1);
                leaf_indices.push(leaf_index as u64);
                ParachainHeader {
                    parachain_header: header.parachain_header.encode(),
                    partial_mmr_leaf: header.partial_mmr_leaf,
                    para_id: client_state.para_id,
                    parachain_heads_proof: header.parachain_heads_proof,
                    heads_leaf_index: header.heads_leaf_index,
                    heads_total_count: header.heads_total_count,
                    extrinsic_proof: header.extrinsic_proof,
                    timestamp_extrinsic: header.timestamp_extrinsic,
                }
            })
            .collect::<Vec<_>>();

        let leaf_count =
            (client_state.to_leaf_index(light_client_state.latest_beefy_height) + 1) as u64;

        let parachain_update_proof = ParachainsUpdateProof {
            parachain_headers,
            mmr_proof: BatchProof {
                leaf_indices,
                leaf_count,
                items: header
                    .mmr_proofs
                    .into_iter()
                    .map(|item| {
                        H256::decode(&mut &*item).map_err(|e| {
                            Error::beefy(BeefyError::invalid_mmr_update(format!("{:?}", e)))
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            },
        };

        // Perform the parachain header verification
        light_client
            .verify_parachain_headers(light_client_state, parachain_update_proof)
            .map_err(|e| Error::beefy(BeefyError::invalid_mmr_update(format!("{:?}", e))))
    }

    fn update_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        let mut parachain_cs_states = vec![];
        // Extract the new client state from the verified header
        let mut client_state = client_state
            .from_header(header.clone())
            .map_err(Error::beefy)?;
        let mut latest_para_height = client_state.latest_para_height;
        for header in header.parachain_headers {
            // Skip genesis block of parachains since it has no timestamp or ibc root
            if header.parachain_header.number == 0 {
                continue;
            }
            if latest_para_height < header.parachain_header.number {
                latest_para_height = header.parachain_header.number;
            }
            let height = Height::new(
                client_state.para_id as u64,
                header.parachain_header.number as u64,
            );
            // Skip duplicate consensus states
            if ctx.consensus_state(&client_id, height).is_ok() {
                continue;
            }
            parachain_cs_states.push((
                height,
                AnyConsensusState::Beefy(ConsensusState::from_header(header)?),
            ))
        }

        client_state.latest_para_height = latest_para_height;

        Ok((
            client_state,
            ConsensusUpdateResult::Batch(parachain_cs_states),
        ))
    }

    fn update_state_on_misbehaviour(
        &self,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        let latest_para_height = header
            .parachain_headers
            .into_iter()
            .map(|header| header.parachain_header.number)
            .max();
        let frozen_height = latest_para_height
            .map(|height| Height::new(client_state.para_id.into(), height.into()))
            .unwrap_or(Height::new(
                client_state.para_id.into(),
                client_state.latest_para_height.into(),
            ));
        client_state
            .with_frozen_height(frozen_height)
            .map_err(|e| Error::beefy(BeefyError::implementation_specific(e.to_string())))
    }

    fn check_for_misbehaviour(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: ClientId,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<bool, Error> {
        Ok(false)
    }

    fn verify_upgrade_and_update_state(
        &self,
        _client_state: &Self::ClientState,
        _consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: Vec<u8>,
        _proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        // TODO:
        Err(Error::beefy(BeefyError::implementation_specific(
            "Not implemented".to_string(),
        )))
    }

    fn verify_client_consensus_state(
        &self,
        _ctx: &dyn ReaderContext,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        let path = ClientConsensusStatePath {
            client_id: client_id.clone(),
            epoch: consensus_height.revision_number,
            height: consensus_height.revision_height,
        };
        let value = expected_consensus_state.encode_vec();
        verify_membership::<HostFunctions, _>(prefix, proof, root, path, value)
    }

    // Consensus state will be verified in the verification functions  before these are called
    fn verify_connection_state(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        let path = ConnectionsPath(connection_id.clone());
        let value = expected_connection_end.encode_vec();
        verify_membership::<HostFunctions, _>(prefix, proof, root, path, value)
    }

    fn verify_channel_state(
        &self,
        _ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        let path = ChannelEndsPath(port_id.clone(), *channel_id);
        let value = expected_channel_end.encode_vec();
        verify_membership::<HostFunctions, _>(prefix, proof, root, path, value)
    }

    fn verify_client_full_state(
        &self,
        _ctx: &dyn ReaderContext,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: &AnyClientState,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        let path = ClientStatePath(client_id.clone());
        let value = expected_client_state.encode_vec();
        verify_membership::<HostFunctions, _>(prefix, proof, root, path, value)
    }

    fn verify_packet_data(
        &self,
        ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let commitment_path = CommitmentsPath {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
        };

        verify_membership::<HostFunctions, _>(
            connection_end.counterparty().prefix(),
            proof,
            root,
            commitment_path,
            commitment.into_vec(),
        )
    }

    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack: AcknowledgementCommitment,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let ack_path = AcksPath {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
        };
        verify_membership::<HostFunctions, _>(
            connection_end.counterparty().prefix(),
            proof,
            root,
            ack_path,
            ack.into_vec(),
        )
    }

    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let seq_bytes = codec::Encode::encode(&u64::from(sequence));

        let seq_path = SeqRecvsPath(port_id.clone(), *channel_id);
        verify_membership::<HostFunctions, _>(
            connection_end.counterparty().prefix(),
            proof,
            root,
            seq_path,
            seq_bytes,
        )
    }

    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ReaderContext,
        _client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        client_state.verify_height(height)?;
        verify_delay_passed(ctx, height, connection_end)?;

        let receipt_path = ReceiptsPath {
            port_id: port_id.clone(),
            channel_id: *channel_id,
            sequence,
        };
        verify_non_membership::<HostFunctions, _>(
            connection_end.counterparty().prefix(),
            proof,
            root,
            receipt_path,
        )
    }
}

fn verify_membership<HostFunctions: HostFunctionsProvider, P: Into<Path>>(
    prefix: &CommitmentPrefix,
    proof: &CommitmentProofBytes,
    root: &CommitmentRoot,
    path: P,
    value: Vec<u8>,
) -> Result<(), Error> {
    if root.as_bytes().len() != 32 {
        return Err(Error::beefy(BeefyError::invalid_commitment_root()));
    }
    let path: Path = path.into();
    let path = path.to_string();
    let mut key = prefix.as_bytes().to_vec();
    key.extend(path.as_bytes());
    let trie_proof: Vec<u8> = proof.clone().into();
    let trie_proof: Vec<Vec<u8>> = codec::Decode::decode(&mut &*trie_proof)
        .map_err(|e| Error::beefy(BeefyError::scale_decode(e)))?;
    let root = H256::from_slice(root.as_bytes());
    HostFunctions::verify_membership_trie_proof(root.as_fixed_bytes(), &trie_proof, &key, &value)
}

fn verify_non_membership<HostFunctions: HostFunctionsProvider, P: Into<Path>>(
    prefix: &CommitmentPrefix,
    proof: &CommitmentProofBytes,
    root: &CommitmentRoot,
    path: P,
) -> Result<(), Error> {
    if root.as_bytes().len() != 32 {
        return Err(Error::beefy(BeefyError::invalid_commitment_root()));
    }
    let path: Path = path.into();
    let path = path.to_string();
    let mut key = prefix.as_bytes().to_vec();
    key.extend(path.as_bytes());
    let trie_proof: Vec<u8> = proof.clone().into();
    let trie_proof: Vec<Vec<u8>> = codec::Decode::decode(&mut &*trie_proof)
        .map_err(|e| Error::beefy(BeefyError::scale_decode(e)))?;
    let root = H256::from_slice(root.as_bytes());
    HostFunctions::verify_non_membership_trie_proof(root.as_fixed_bytes(), &trie_proof, &key)
}

fn verify_delay_passed(
    ctx: &dyn ReaderContext,
    height: Height,
    connection_end: &ConnectionEnd,
) -> Result<(), Error> {
    let current_timestamp = ctx.host_timestamp();
    let current_height = ctx.host_height();

    let client_id = connection_end.client_id();
    let processed_time = ctx.client_update_time(client_id, height).map_err(|_| {
        Error::beefy(BeefyError::processed_time_not_found(
            client_id.clone(),
            height,
        ))
    })?;
    let processed_height = ctx.client_update_height(client_id, height).map_err(|_| {
        Error::beefy(BeefyError::processed_height_not_found(
            client_id.clone(),
            height,
        ))
    })?;

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

pub fn downcast_consensus_state(cs: AnyConsensusState) -> Result<ConsensusState, Error> {
    downcast!(
        cs => AnyConsensusState::Beefy
    )
    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))
}
