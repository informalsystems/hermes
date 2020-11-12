use crossbeam_channel as channel;

use ibc::{
    events::IBCEvent,
    ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader},
    ics03_connection::connection::ConnectionEnd,
    ics03_connection::msgs::ConnectionMsgType,
    ics23_commitment::commitment::CommitmentPrefix,
    ics23_commitment::merkle::MerkleProof,
    ics24_host::identifier::ChainId,
    ics24_host::identifier::{ClientId, ConnectionId},
    Height,
};

// FIXME: the handle should not depend on tendermint-specific types
use tendermint::account::Id as AccountId;
use tendermint_light_client::types::SignedHeader;

use crate::{
    chain::QueryResponse,
    error::{Error, Kind},
    foreign_client::ForeignClient,
    keyring::store::KeyEntry,
    msgs::{EncodedTransaction, Packet},
};

use super::{reply_channel, ChainHandle, HandleInput, ReplyTo, Subscription};

#[derive(Debug, Clone)]
pub struct ProdChainHandle {
    chain_id: ChainId,
    sender: channel::Sender<HandleInput>,
}

impl ProdChainHandle {
    pub fn new(chain_id: ChainId, sender: channel::Sender<HandleInput>) -> Self {
        Self { chain_id, sender }
    }

    fn send<F, O>(&self, f: F) -> Result<O, Error>
    where
        F: FnOnce(ReplyTo<O>) -> HandleInput,
    {
        let (sender, receiver) = reply_channel();
        let input = f(sender);

        self.sender
            .send(input)
            .map_err(|e| Kind::Channel.context(e))?;

        receiver.recv().map_err(|e| Kind::Channel.context(e))?
    }
}

impl ChainHandle for ProdChainHandle {
    fn id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, Error> {
        self.send(|reply_to| HandleInput::Subscribe { reply_to })
    }

    fn query(
        &self,
        path: ibc::ics24_host::Path,
        height: Height,
        prove: bool,
    ) -> Result<QueryResponse, Error> {
        self.send(|reply_to| HandleInput::Query {
            path,
            height,
            prove,
            reply_to,
        })
    }

    fn send_tx(
        &self,
        proto_msgs: Vec<prost_types::Any>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<String, Error> {
        todo!()
    }

    fn get_header(&self, height: Height) -> Result<AnyHeader, Error> {
        self.send(|reply_to| HandleInput::GetHeader { height, reply_to })
    }

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, Error> {
        self.send(|reply_to| HandleInput::GetMinimalSet { from, to, reply_to })
    }

    fn key_and_signer(&self, key_file_contents: String) -> Result<(KeyEntry, AccountId), Error> {
        self.send(|reply_to| HandleInput::KeyAndSigner {
            key_file_contents,
            reply_to,
        })
    }

    fn submit(&self, transaction: EncodedTransaction) -> Result<(), Error> {
        self.send(|reply_to| HandleInput::Submit {
            transaction,
            reply_to,
        })
    }

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, Error> {
        self.send(|reply_to| HandleInput::CreatePacket { event, reply_to })
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        self.send(|reply_to| HandleInput::QueryLatestHeight { reply_to })
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error> {
        self.send(|reply_to| HandleInput::QueryClientState {
            client_id: client_id.clone(),
            height,
            reply_to,
        })
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.send(|reply_to| HandleInput::QueryCommitmentPrefix { reply_to })
    }

    fn query_compatible_versions(&self) -> Result<Vec<String>, Error> {
        self.send(|reply_to| HandleInput::QueryCompatibleVersions { reply_to })
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error> {
        self.send(|reply_to| HandleInput::QueryConnection {
            connection_id: connection_id.clone(),
            height,
            reply_to,
        })
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.send(|reply_to| HandleInput::ProvenClientState {
            client_id: client_id.clone(),
            height,
            reply_to,
        })
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        self.send(|reply_to| HandleInput::ProvenConnection {
            connection_id: connection_id.clone(),
            height,
            reply_to,
        })
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.send(|reply_to| HandleInput::ProvenClientConsensus {
            client_id: client_id.clone(),
            consensus_height,
            height,
            reply_to,
        })
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
    ) -> Result<AnyHeader, Error> {
        self.send(|reply_to| HandleInput::BuildHeader {
            trusted_height,
            target_height,
            reply_to,
        })
    }

    fn build_client_state(&self, height: Height) -> Result<AnyClientState, Error> {
        self.send(|reply_to| HandleInput::BuildClientState { height, reply_to })
    }

    fn build_consensus_state(&self, height: Height) -> Result<AnyConsensusState, Error> {
        self.send(|reply_to| HandleInput::BuildConsensusState { height, reply_to })
    }

    fn build_connection_proofs(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<ibc::proofs::Proofs, Error> {
        self.send(|reply_to| HandleInput::BuildConnectionProofs {
            message_type,
            connection_id: connection_id.clone(),
            client_id: client_id.clone(),
            height,
            reply_to,
        })
    }
}
