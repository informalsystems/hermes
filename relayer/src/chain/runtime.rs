use std::time::Duration;

use crossbeam_channel as channel;
use thiserror::Error;

use ibc::{
    ics02_client::{
        client_def::{AnyClientState, AnyConsensusState, AnyHeader},
        header::Header,
        state::{ClientState, ConsensusState},
    },
    ics03_connection::{connection::ConnectionEnd, msgs::ConnectionMsgType},
    ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
    ics24_host::identifier::{ChainId, ClientId, ConnectionId},
    ics24_host::Path,
    proofs::Proofs,
    Height,
};

// FIXME: the handle should not depend on tendermint-specific types
use tendermint::account::Id as AccountId;

// use crate::foreign_client::ForeignClient;

use crate::{
    config::ChainConfig,
    error::{Error, Kind},
    keyring::store::KeyEntry,
    light_client::LightBlock,
    light_client::{tendermint::LightClient as TMLightClient, LightClient},
    msgs::{Datagram, EncodedTransaction, IBCEvent, Packet},
    util::block_on,
};

use super::{
    handle::{ChainHandle, HandleInput, ProdChainHandle, ReplyTo, Subscription},
    Chain, CosmosSDKChain, QueryResponse,
};

pub struct ChainRuntime<C: Chain> {
    chain: C,
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
    light_client: Box<dyn LightClient<C>>,
}

impl ChainRuntime<CosmosSDKChain> {
    pub fn cosmos_sdk(config: ChainConfig, light_client: TMLightClient) -> Result<Self, Error> {
        let chain = CosmosSDKChain::from_config(config)?;
        Ok(Self::new(chain, light_client))
    }
}

impl<C: Chain> ChainRuntime<C> {
    pub fn new(chain: C, light_client: impl LightClient<C> + 'static) -> Self {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        Self {
            chain,
            sender,
            receiver,
            light_client: Box::new(light_client),
        }
    }

    pub fn handle(&self) -> impl ChainHandle {
        let chain_id = self.chain.id().clone();
        let sender = self.sender.clone();

        ProdChainHandle::new(chain_id, sender)
    }

    pub fn run(mut self) -> Result<(), Error> {
        loop {
            channel::select! {
                recv(self.receiver) -> event => {
                    match event {
                        Ok(HandleInput::Terminate { reply_to }) => {
                            reply_to.send(Ok(())).map_err(|_| Kind::Channel)?;
                            break;
                        }

                        Ok(HandleInput::Subscribe { reply_to }) => {
                            self.subscribe(reply_to)?
                        },

                        Ok(HandleInput::Query { path, height, prove, reply_to, }) => {
                            self.query(path, height, prove, reply_to)?
                        },

                        Ok(HandleInput::GetMinimalSet { from, to, reply_to }) => {
                            self.get_minimal_set(from, to, reply_to)?
                        }

                        // Ok(HandleInput::GetHeader { height, reply_to }) => {
                        //     self.get_header(height, reply_to)?
                        // }
                        //
                        // Ok(HandleInput::Submit { transaction, reply_to, }) => {
                        //     self.submit(transaction, reply_to)?
                        // },
                        //
                        // Ok(HandleInput::CreatePacket { event, reply_to }) => {
                        //     self.create_packet(event, reply_to)?
                        // }

                        Ok(HandleInput::KeyAndSigner { key_file_contents, reply_to }) => {
                            self.key_and_signer(key_file_contents, reply_to)?
                        }

                        Ok(HandleInput::BuildHeader { trusted_height, target_height, reply_to }) => {
                            self.build_header(trusted_height, target_height, reply_to)?
                        }
                        Ok(HandleInput::BuildClientState { height, reply_to }) => {
                            self.build_client_state(height, reply_to)?
                        }
                        Ok(HandleInput::BuildConsensusState { height, reply_to }) => {
                            self.build_consensus_state(height, reply_to)?
                        }
                        Ok(HandleInput::BuildConnectionProofs { message_type, connection_id, client_id, height, reply_to }) => {
                            self.build_connection_proofs(message_type, connection_id, client_id, height, reply_to)?
                        },

                        Ok(HandleInput::QueryLatestHeight { reply_to }) => {
                            self.query_latest_height(reply_to)?
                        }
                        Ok(HandleInput::QueryClientState { client_id, height, reply_to }) => {
                            self.query_client_state(client_id, height, reply_to)?
                        },

                        Ok(HandleInput::QueryCommitmentPrefix { reply_to }) => {
                            self.query_commitment_prefix(reply_to)?
                        },

                        Ok(HandleInput::QueryCompatibleVersions { reply_to }) => {
                            self.query_compatible_versions(reply_to)?
                        },

                        Ok(HandleInput::QueryConnection { connection_id, height, reply_to }) => {
                            self.query_connection(connection_id, height, reply_to)?
                        },

                        Ok(HandleInput::ProvenClientState { client_id, height, reply_to }) => {
                            self.proven_client_state(client_id, height, reply_to)?
                        },

                        Ok(HandleInput::ProvenConnection { connection_id, height, reply_to }) => {
                            self.proven_connection(connection_id, height, reply_to)?
                        },

                        Ok(HandleInput::ProvenClientConsensus { client_id, consensus_height, height, reply_to }) => {
                            self.proven_client_consensus(client_id, consensus_height, height, reply_to)?
                        },
                        Err(e) => todo!(),
                    }
                },
            }
        }

        Ok(())
    }

    fn subscribe(&self, reply_to: ReplyTo<Subscription>) -> Result<(), Error> {
        todo!()
    }

    fn query(
        &self,
        path: Path,
        height: Height,
        prove: bool,
        reply_to: ReplyTo<QueryResponse>,
    ) -> Result<(), Error> {
        if !path.is_provable() & prove {
            reply_to
                .send(Err(Kind::NonProvableData.into()))
                .map_err(|e| Kind::Channel.context(e))?;
            return Ok(());
        }

        let response = self.chain.query(path, height, prove);

        // Verify response proof, if requested.
        if prove {
            dbg!("TODO: implement proof verification."); // TODO: Verify proof
        }

        reply_to
            .send(response)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_latest_height(&self, reply_to: ReplyTo<Height>) -> Result<(), Error> {
        let latest_height = self.chain.query_latest_height();

        reply_to
            .send(latest_height)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    // fn get_header(&self, height: Height, reply_to: ReplyTo<AnyHeader>) -> Result<(), Error> {
    //     let light_block = self.light_client.verify_to_target(height);
    //     let header: Result<AnyHeader, _> = todo!(); // light_block.map(|lb| lb.signed_header().wrap_any());

    //     reply_to
    //         .send(header)
    //         .map_err(|e| Kind::Channel.context(e))?;

    //     Ok(())
    // }

    fn get_minimal_set(
        &self,
        from: Height,
        to: Height,
        reply_to: ReplyTo<Vec<AnyHeader>>,
    ) -> Result<(), Error> {
        todo!()
    }

    // fn submit(&self, transaction: EncodedTransaction, reply_to: ReplyTo<()>) -> Result<(), Error> {
    //     todo!()
    // }

    // fn create_packet(&self, event: IBCEvent, reply_to: ReplyTo<Packet>) -> Result<(), Error> {
    //     todo!()
    // }

    fn key_and_signer(
        &mut self,
        key_file_contents: String,
        reply_to: ReplyTo<(KeyEntry, AccountId)>,
    ) -> Result<(), Error> {
        let result = self.chain.key_and_signer(&key_file_contents);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        reply_to: ReplyTo<AnyHeader>,
    ) -> Result<(), Error> {
        let header = {
            // Get the light block at target_height from chain.
            let target_light_block = self.light_client.verify_to_target(target_height)?;

            // Get the light block at trusted_height from the chain.
            let trusted_light_block = self.light_client.verify_to_target(trusted_height)?;

            let header = self
                .chain
                .build_header(target_light_block, trusted_light_block)?;

            Ok(header.wrap_any())
        };

        reply_to
            .send(header)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    /// Constructs a client state for the given height
    fn build_client_state(
        &self,
        height: Height,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        let client_state = self
            .chain
            .build_client_state(height)
            .map(|cs| cs.wrap_any());

        reply_to
            .send(client_state)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    /// Constructs a consensus state for the given height
    fn build_consensus_state(
        &self,
        height: Height,
        reply_to: ReplyTo<AnyConsensusState>,
    ) -> Result<(), Error> {
        let latest_light_block = self.light_client.verify_to_target(height)?;

        let consensus_state = self
            .chain
            .build_consensus_state(latest_light_block)
            .map(|cs| cs.wrap_any());

        reply_to
            .send(consensus_state)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn build_connection_proofs(
        &self,
        message_type: ConnectionMsgType,
        connection_id: ConnectionId,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<Proofs>,
    ) -> Result<(), Error> {
        let proofs =
            self.chain
                .build_connection_proofs(message_type, &connection_id, &client_id, height);

        reply_to
            .send(proofs)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_client_state(
        &self,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        let client_state = self
            .chain
            .query_client_state(&client_id, height)
            .map(|cs| cs.wrap_any());

        reply_to
            .send(client_state)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_commitment_prefix(&self, reply_to: ReplyTo<CommitmentPrefix>) -> Result<(), Error> {
        let prefix = self.chain.query_commitment_prefix();

        reply_to
            .send(prefix)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_compatible_versions(&self, reply_to: ReplyTo<Vec<String>>) -> Result<(), Error> {
        let versions = self.chain.query_compatible_versions();

        reply_to
            .send(versions)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_connection(
        &self,
        connection_id: ConnectionId,
        height: Height,
        reply_to: ReplyTo<ConnectionEnd>,
    ) -> Result<(), Error> {
        let connection_end = self.chain.query_connection(&connection_id, height);

        reply_to
            .send(connection_end)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn proven_client_state(
        &self,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .proven_client_state(&client_id, height)
            .map(|(cs, mp)| (cs.wrap_any(), mp));

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn proven_connection(
        &self,
        connection_id: ConnectionId,
        height: Height,
        reply_to: ReplyTo<(ConnectionEnd, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self.chain.proven_connection(&connection_id, height);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn proven_client_consensus(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        height: Height,
        reply_to: ReplyTo<(AnyConsensusState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .proven_client_consensus(&client_id, consensus_height, height)
            .map(|(cs, mp)| (cs.wrap_any(), mp));

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }
}
