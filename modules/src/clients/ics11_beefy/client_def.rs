use beefy_client::primitives::{ParachainHeader, ParachainsUpdateProof};
use beefy_client::traits::{HostFunctions, StorageRead, StorageWrite};
use beefy_client::BeefyLightClient;
use codec::Encode;
use core::convert::TryInto;
use pallet_mmr_primitives::BatchProof;
use sp_core::H256;
use tendermint_proto::Protobuf;

use crate::clients::ics11_beefy::client_state::ClientState;
use crate::clients::ics11_beefy::consensus_state::ConsensusState;
use crate::clients::ics11_beefy::error::Error as BeefyError;
use crate::clients::ics11_beefy::header::BeefyHeader;
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_def::{ClientDef, ConsensusUpdateResult};
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::context::ClientReader;
use crate::core::ics02_client::error::Error;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::packet::Sequence;

use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};

use crate::core::ics24_host::identifier::ConnectionId;
use crate::core::ics24_host::identifier::{ChannelId, ClientId, PortId};
use crate::core::ics24_host::Path;
use crate::prelude::*;
use crate::Height;

use crate::core::ics24_host::path::{
    AcksPath, ChannelEndsPath, ClientConsensusStatePath, ClientStatePath, CommitmentsPath,
    ConnectionsPath, ReceiptsPath, SeqRecvsPath,
};
use crate::downcast;

/// Methods definitions specific to Beefy Light Client operation
pub trait BeefyLCStore: StorageRead + StorageWrite + HostFunctions + Clone + Default {
    /// This function should verify membership in a trie proof using parity's sp-trie package
    /// with a BlakeTwo256 Hasher
    fn verify_membership_trie_proof(
        root: &H256,
        proof: &Vec<Vec<u8>>,
        key: &[u8],
        value: &[u8],
    ) -> Result<(), Error>;
    /// This function should verify non membership in a trie proof using parity's sp-trie package
    /// with a BlakeTwo256 Hasher
    fn verify_non_membership_trie_proof(
        root: &H256,
        proof: &Vec<Vec<u8>>,
        key: &[u8],
    ) -> Result<(), Error>;
    fn store_latest_parachains_height(para_id_and_heights: Vec<(u64, u64)>) -> Result<(), Error>;
    fn get_parachain_latest_height(para_id: u64) -> Result<u64, Error>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BeefyClient<Store: BeefyLCStore> {
    store: Store,
}

impl<Store: BeefyLCStore> ClientDef for BeefyClient<Store> {
    type Header = BeefyHeader;
    type ClientState = ClientState;
    type ConsensusState = ConsensusState;

    fn verify_header(
        &self,
        _ctx: &dyn ClientReader,
        _client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error> {
        let mut light_client = BeefyLightClient::<_, Store>::new(self.store.clone());
        if let Some(mmr_update) = header.mmr_update_proof {
            light_client
                .ingest_mmr_root_with_proof(mmr_update)
                .map_err(|e| Error::beefy(BeefyError::invalid_mmr_update(format!("{:?}", e))))?;
        }

        let mut leaf_indices = vec![];
        let parachain_headers = header
            .parachain_headers
            .clone()
            .into_iter()
            .map(|header| {
                let leaf_index =
                    client_state.to_leaf_index(header.partial_mmr_leaf.parent_number_and_hash.0);
                leaf_indices.push(leaf_index as u64);
                ParachainHeader {
                    parachain_header: header.parachain_header.encode(),
                    partial_mmr_leaf: header.partial_mmr_leaf,
                    para_id: header.para_id,
                    parachain_heads_proof: header.parachain_heads_proof,
                    heads_leaf_index: header.heads_leaf_index,
                    heads_total_count: header.heads_total_count,
                    extrinsic_proof: header.extrinsic_proof,
                }
            })
            .collect::<Vec<_>>();
        let leaf_count = (client_state.to_leaf_index(client_state.latest_beefy_height) + 1) as u64;

        let parachain_update_proof = ParachainsUpdateProof {
            parachain_headers,
            mmr_proof: BatchProof {
                leaf_indices,
                leaf_count,
                items: header
                    .mmr_proofs
                    .into_iter()
                    .map(|item| H256::from_slice(&item))
                    .collect(),
            },
        };

        light_client
            .verify_parachain_headers(parachain_update_proof)
            .map_err(|e| Error::beefy(BeefyError::invalid_mmr_update(format!("{:?}", e))))
    }

    fn update_state(
        &self,
        ctx: &dyn ClientReader,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        let mut parachain_cs_states = vec![];
        for header in header.parachain_headers {
            let height = Height::new(header.para_id as u64, header.parachain_header.number as u64);
            // Skip duplicate consensus states
            if let Ok(_) = ctx.consensus_state(&client_id, height) {
                continue;
            }
            parachain_cs_states.push((
                height,
                AnyConsensusState::Beefy(ConsensusState::from(header)),
            ))
        }

        let best_cs_state = if let Some(cs_state) = last_seen_cs {
            cs_state
        } else {
            trusted_consensus_state
        };

        let best_para_height = if let Some(best_height) = last_seen_height {
            best_height
        } else {
            latest_para_height
        };
        let mmr_state = self
            .store
            .mmr_state()
            .map_err(|e| Error::beefy(BeefyError::implementation_specific(format!("{:?}", e))))?;
        let authorities = self
            .store
            .authority_set()
            .map_err(|e| Error::beefy(BeefyError::implementation_specific(format!("{:?}", e))))?;

        let client_state = client_state.with_updates(mmr_state, authorities);

        Ok((
            client_state,
            ConsensusUpdateResult::Batch(parachain_cs_states),
        ))
    }

    fn update_state_on_misbehaviour(
        &self,
        client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        let mmr_state = self
            .store
            .mmr_state()
            .map_err(|_| Error::beefy(BeefyError::missing_latest_height()))?;
        client_state
            .with_frozen_height(Height::new(0, mmr_state.latest_beefy_height as u64))
            .map_err(|e| Error::beefy(BeefyError::implementation_specific(e.to_string())))
    }

    fn check_for_misbehaviour(
        &self,
        _ctx: &dyn ClientReader,
        _client_id: ClientId,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<bool, Error> {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error> {
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;

        let path = ClientConsensusStatePath {
            client_id: client_id.clone(),
            epoch: consensus_height.revision_number,
            height: consensus_height.revision_height,
        };
        let value = expected_consensus_state.encode_vec().unwrap();
        verify_membership::<Store, _>(prefix, proof, root, path, value)
    }

    fn verify_connection_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;

        let path = ConnectionsPath(connection_id.clone());
        let value = expected_connection_end.encode_vec().unwrap();
        verify_membership::<Store, _>(prefix, proof, root, path, value)
    }

    fn verify_channel_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;

        let path = ChannelEndsPath(port_id.clone(), channel_id.clone());
        let value = expected_channel_end.encode_vec().unwrap();
        verify_membership::<Store, _>(prefix, proof, root, path, value)
    }

    fn verify_client_full_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: &AnyClientState,
    ) -> Result<(), Error> {
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;

        let path = ClientStatePath(client_id.clone());
        let value = expected_client_state.encode_vec().unwrap();
        verify_membership::<Store, _>(prefix, proof, root, path, value)
    }

    fn verify_packet_data(
        &self,
        ctx: &dyn ChannelReader,
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
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;
        verify_delay_passed(ctx, height, connection_end)?;

        let commitment_path = CommitmentsPath {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
        };

        verify_membership::<Store, _>(
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
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;
        verify_delay_passed(ctx, height, connection_end)?;

        let ack_path = AcksPath {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
        };
        verify_membership::<Store, _>(
            connection_end.counterparty().prefix(),
            proof,
            root,
            ack_path,
            ack.into_vec(),
        )
    }

    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ChannelReader,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;
        verify_delay_passed(ctx, height, connection_end)?;

        let seq_bytes = codec::Encode::encode(&u64::from(sequence));

        let seq_path = SeqRecvsPath(port_id.clone(), channel_id.clone());
        verify_membership::<Store, _>(
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
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        client_state
            .verify_parachain_height::<Store>(height)
            .map_err(|e| Error::beefy(e))?;
        verify_delay_passed(ctx, height, connection_end)?;

        let receipt_path = ReceiptsPath {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            sequence,
        };
        verify_non_membership::<Store, _>(
            connection_end.counterparty().prefix(),
            proof,
            root,
            receipt_path,
        )
    }

    fn verify_upgrade_and_update_state(
        &self,
        _client_state: &Self::ClientState,
        _consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: Vec<u8>,
        _proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        todo!()
    }
}

fn verify_membership<Verifier: BeefyLCStore, P: Into<Path>>(
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
    let path = vec![prefix.as_bytes(), path.as_bytes()];
    let key = codec::Encode::encode(&path);
    let trie_proof: Vec<u8> = proof.clone().into();
    let trie_proof: Vec<Vec<u8>> = codec::Decode::decode(&mut &*trie_proof)
        .map_err(|e| Error::beefy(BeefyError::scale_decode(e)))?;
    let root = H256::from_slice(root.as_bytes());
    Verifier::verify_membership_trie_proof(&root, &trie_proof, &key, &value)
}

fn verify_non_membership<Verifier: BeefyLCStore, P: Into<Path>>(
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
    let path = vec![prefix.as_bytes(), path.as_bytes()];
    let key = codec::Encode::encode(&path);
    let trie_proof: Vec<u8> = proof.clone().into();
    let trie_proof: Vec<Vec<u8>> = codec::Decode::decode(&mut &*trie_proof)
        .map_err(|e| Error::beefy(BeefyError::scale_decode(e)))?;
    let root = H256::from_slice(root.as_bytes());
    Verifier::verify_non_membership_trie_proof(&root, &trie_proof, &key)
}

fn verify_delay_passed(
    ctx: &dyn ChannelReader,
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
