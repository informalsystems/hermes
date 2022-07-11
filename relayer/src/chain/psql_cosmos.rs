#![allow(unused_variables, dead_code)]

use alloc::sync::Arc;
use core::future::Future;

use semver::Version;
use sqlx::postgres::{PgPool, PgPoolOptions};
use tendermint_rpc::endpoint::broadcast::tx_sync;
use tracing::{info, span, Level};

use super::requests::{QueryBlockRequest, QueryTxRequest};
use ibc::{
    core::{
        ics02_client::{
            client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight},
            client_state::{AnyClientState, IdentifiedAnyClientState},
            events::UpdateClient,
            misbehaviour::MisbehaviourEvidence,
        },
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics04_channel::{
            channel::{ChannelEnd, IdentifiedChannelEnd},
            packet::Sequence,
        },
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::{ChainId, ConnectionId},
    },
    events::IbcEvent,
    Height,
};

use super::cosmos::query::account::get_or_fetch_account;
use crate::chain::cosmos::CosmosSdkChain;
use crate::chain::psql_cosmos::batch::send_batched_messages_and_wait_commit;
use crate::chain::psql_cosmos::query::{query_blocks, query_txs};
use crate::denom::DenomTrace;
use crate::{
    account::Balance,
    chain::{
        client::ClientSettings,
        endpoint::{ChainEndpoint, ChainStatus, HealthCheck},
        requests::*,
        tracking::TrackedMsgs,
    },
    config::ChainConfig,
    error::Error,
    event::monitor::{EventReceiver, TxMonitorCmd},
    keyring::{KeyEntry, KeyRing},
    light_client::{tendermint::LightClient as TmLightClient, LightClient, Verified},
};

pub mod batch;
pub mod query;
pub mod wait;

flex_error::define_error! {
    PsqlError {
        MissingConnectionConfig
            { chain_id: ChainId }
            |e| { format_args!("missing `psql_conn` config for chain '{}'", e.chain_id) }
    }
}

pub struct PsqlChain {
    chain: CosmosSdkChain,
    pool: PgPool,
    rt: Arc<tokio::runtime::Runtime>,
}

impl PsqlChain {
    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        crate::time!("block_on");
        self.rt.block_on(f)
    }

    async fn do_send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("do_send_messages_and_wait_commit");

        let _span =
            span!(Level::DEBUG, "do_send_messages_and_wait_commit", id = %tracked_msgs.tracking_id()).entered();

        let proto_msgs = tracked_msgs.msgs;

        let key_entry = self.chain.key()?;

        let account = get_or_fetch_account(
            &self.chain.grpc_addr,
            &key_entry.account,
            &mut self.chain.account,
        )
        .await?;

        send_batched_messages_and_wait_commit(
            // TODO AZ
            &self.pool,
            &self.chain.tx_config,
            self.chain.config.max_msg_num,
            self.chain.config.max_tx_size,
            &key_entry,
            account,
            &self.chain.config.memo_prefix,
            proto_msgs,
        )
        .await
    }
}
impl ChainEndpoint for PsqlChain {
    type LightBlock = <CosmosSdkChain as ChainEndpoint>::LightBlock;

    type Header = <CosmosSdkChain as ChainEndpoint>::Header;

    type ConsensusState = <CosmosSdkChain as ChainEndpoint>::ConsensusState;

    type ClientState = <CosmosSdkChain as ChainEndpoint>::ClientState;

    type LightClient = PsqlLightClient;

    fn bootstrap(config: ChainConfig, rt: Arc<tokio::runtime::Runtime>) -> Result<Self, Error> {
        info!("bootsrapping");

        let psql_conn = config
            .psql_conn
            .as_deref()
            .ok_or_else(|| PsqlError::missing_connection_config(config.id.clone()))?;

        let pool = rt
            .block_on(PgPoolOptions::new().max_connections(5).connect(psql_conn))
            .map_err(Error::sqlx)?;

        info!("instantiating chain");

        let chain = CosmosSdkChain::bootstrap(config, rt.clone())?;

        Ok(Self { chain, pool, rt })
    }

    fn init_light_client(&self) -> Result<Self::LightClient, Error> {
        self.chain.init_light_client().map(PsqlLightClient)
    }

    fn init_event_monitor(
        &self,
        rt: Arc<tokio::runtime::Runtime>,
    ) -> Result<(EventReceiver, TxMonitorCmd), Error> {
        self.chain.init_event_monitor(rt)
    }

    fn id(&self) -> &ChainId {
        // let _ = &self.pool;
        // let _ = &self.rt;
        self.chain.id()
    }

    fn shutdown(self) -> Result<(), Error> {
        self.chain.shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        // TODO(romac): Check database connection

        self.chain.health_check()
    }

    fn keybase(&self) -> &KeyRing {
        self.chain.keybase()
    }

    fn keybase_mut(&mut self) -> &mut KeyRing {
        self.chain.keybase_mut()
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
        let runtime = self.rt.clone();
        runtime.block_on(self.do_send_messages_and_wait_commit(tracked_msgs))
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tx_sync::Response>, Error> {
        self.chain.send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&mut self) -> Result<ibc::signer::Signer, Error> {
        self.chain.get_signer()
    }

    fn config(&self) -> ChainConfig {
        ChainEndpoint::config(&self.chain)
    }

    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        self.chain.get_key()
    }

    fn add_key(&mut self, key_name: &str, key: KeyEntry) -> Result<(), Error> {
        self.chain.add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<Version>, Error> {
        self.chain.ibc_version()
    }

    fn query_balance(&self, key_name: Option<String>) -> Result<Balance, Error> {
        self.chain.query_balance(key_name)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.chain.query_commitment_prefix()
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        self.chain.query_application_status()
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.chain.query_clients(request)
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        self.chain.query_client_state(request, include_proof)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.chain.query_consensus_states(request)
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        self.chain.query_consensus_state(request, include_proof)
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.chain.query_upgraded_client_state(request)
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.chain.query_upgraded_consensus_state(request)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.chain.query_connections(request)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.chain.query_client_connections(request)
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        self.chain.query_connection(request, include_proof)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.chain.query_connection_channels(request)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.chain.query_channels(request)
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        self.chain.query_channel(request, include_proof)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.chain.query_channel_client_state(request)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.chain.query_packet_commitments(request)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.chain.query_unreceived_packets(request)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.chain.query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.chain.query_unreceived_acknowledgements(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        self.chain
            .query_next_sequence_receive(request, include_proof)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("query_txs");
        crate::telemetry!(query, self.id(), "query_txs");

        self.block_on(query_txs(&self.pool, self.id(), &request))
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        // Currently the psql tendermint DB does not distinguish between begin and end block events.
        // The SQL query in `query_blocks` returns all block events
        let all_block_events = self.block_on(query_blocks(&self.pool, self.id(), &request))?;
        Ok((all_block_events, vec![]))
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        self.chain.query_host_consensus_state(request)
    }

    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        self.chain.build_client_state(height, settings)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        self.chain.build_consensus_state(light_block)
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: &AnyClientState,
        light_client: &mut Self::LightClient,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        self.chain.build_header(
            trusted_height,
            target_height,
            client_state,
            &mut light_client.0,
        )
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.chain.query_packet_commitment(request, include_proof)
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.chain.query_packet_receipt(request, include_proof)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.chain
            .query_packet_acknowledgement(request, include_proof)
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        self.chain.query_denom_trace(hash)
    }
}

pub struct PsqlLightClient(TmLightClient);

impl LightClient<PsqlChain> for PsqlLightClient {
    fn header_and_minimal_set(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<<PsqlChain as ChainEndpoint>::Header>, Error> {
        self.0.header_and_minimal_set(trusted, target, client_state)
    }

    fn verify(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<<PsqlChain as ChainEndpoint>::LightBlock>, Error> {
        self.0.verify(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &mut self,
        update: UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.0.check_misbehaviour(update, client_state)
    }

    fn fetch(&mut self, height: Height) -> Result<<PsqlChain as ChainEndpoint>::LightBlock, Error> {
        self.0.fetch(height)
    }
}
