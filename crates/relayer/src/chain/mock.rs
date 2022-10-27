use alloc::sync::Arc;
use core::ops::Add;
use core::time::Duration;

use crossbeam_channel as channel;
use tendermint_testgen::light_block::TmLightBlock;
use tokio::runtime::Runtime;

use ibc::clients::ics07_tendermint::client_state::{AllowUpdate, ClientState as TmClientState};
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc::core::ics02_client::events::UpdateClient;
use ibc::core::ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd};
use ibc::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc::core::ics04_channel::context::ChannelReader;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics23_commitment::merkle::MerkleProof;
use ibc::core::ics23_commitment::{commitment::CommitmentPrefix, specs::ProofSpecs};
use ibc::core::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::mock::context::MockContext;
use ibc::mock::host::HostType;
use ibc::relayer::ics18_relayer::context::Ics18Context;
use ibc::signer::Signer;
use ibc::test_utils::get_dummy_account_id;
use ibc::Height;

use crate::account::Balance;
use crate::chain::client::ClientSettings;
use crate::chain::endpoint::{ChainEndpoint, ChainStatus, HealthCheck};
use crate::chain::requests::{
    QueryChannelClientStateRequest, QueryChannelRequest, QueryClientStatesRequest,
    QueryPacketEventDataRequest,
};
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::ChainConfig;
use crate::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use crate::denom::DenomTrace;
use crate::error::Error;
use crate::event::monitor::{EventReceiver, EventSender, TxMonitorCmd};
use crate::event::IbcEventWithHeight;
use crate::keyring::{KeyEntry, KeyRing};
use crate::light_client::Verified;
use crate::light_client::{mock::LightClient as MockLightClient, LightClient};
use crate::misbehaviour::MisbehaviourEvidence;

use super::requests::{
    IncludeProof, QueryChannelsRequest, QueryClientConnectionsRequest, QueryClientStateRequest,
    QueryConnectionChannelsRequest, QueryConnectionRequest, QueryConnectionsRequest,
    QueryConsensusStateRequest, QueryConsensusStatesRequest, QueryHostConsensusStateRequest,
    QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementRequest,
    QueryPacketAcknowledgementsRequest, QueryPacketCommitmentRequest,
    QueryPacketCommitmentsRequest, QueryPacketReceiptRequest, QueryTxRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest, QueryUpgradedClientStateRequest,
    QueryUpgradedConsensusStateRequest,
};
use super::tracking::TrackedMsgs;

/// The representation of a mocked chain as the relayer sees it.
/// The relayer runtime and the light client will engage with the MockChain to query/send tx; the
/// primary interface for doing so is captured by `ICS18Context` which this struct can access via
/// the `context` field.
pub struct MockChain {
    config: ChainConfig,
    context: MockContext,
    light_client: MockLightClient,

    // keep a reference to event sender to prevent it from being dropped
    #[allow(dead_code)]
    event_sender: EventSender,

    event_receiver: EventReceiver,
}

impl MockChain {
    fn trusting_period(&self) -> Duration {
        self.config
            .trusting_period
            .unwrap_or_else(|| Duration::from_secs(14 * 24 * 60 * 60)) // 14 days
    }
}

impl ChainEndpoint for MockChain {
    type LightBlock = TmLightBlock;
    type Header = TendermintHeader;
    type ConsensusState = TendermintConsensusState;
    type ClientState = TmClientState;

    fn bootstrap(config: ChainConfig, _rt: Arc<Runtime>) -> Result<Self, Error> {
        let (event_sender, event_receiver) = channel::unbounded();

        let context = MockContext::new(
            config.id.clone(),
            HostType::SyntheticTendermint,
            50,
            Height::new(config.id.version(), 20).unwrap(),
        );

        let light_client = MockLightClient::new(config.id.clone());

        Ok(MockChain {
            config,
            light_client,
            context,
            event_sender,
            event_receiver,
        })
    }

    fn init_event_monitor(
        &self,
        _rt: Arc<Runtime>,
    ) -> Result<(EventReceiver, TxMonitorCmd), Error> {
        let (tx, _) = crossbeam_channel::unbounded();
        Ok((self.event_receiver.clone(), tx))
    }

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        Ok(HealthCheck::Healthy)
    }

    fn shutdown(self) -> Result<(), Error> {
        Ok(())
    }

    fn keybase(&self) -> &KeyRing {
        unimplemented!()
    }

    fn keybase_mut(&mut self) -> &mut KeyRing {
        unimplemented!()
    }

    fn verify_header(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        self.light_client
            .verify(trusted, target, client_state)
            .map(|v| v.target)
    }

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.light_client.check_misbehaviour(update, client_state)
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        // Use the ICS18Context interface to submit the set of messages.
        let events = self.context.send(tracked_msgs.msgs).map_err(Error::ics18)?;

        Ok(events
            .into_iter()
            .map(|ev| IbcEventWithHeight::new(ev, Height::new(0, 1).unwrap()))
            .collect())
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        _tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        todo!()
    }

    fn get_signer(&mut self) -> Result<Signer, Error> {
        Ok(get_dummy_account_id())
    }

    fn config(&self) -> ChainConfig {
        self.config.clone()
    }

    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        unimplemented!()
    }

    fn add_key(&mut self, _key_name: &str, _key: KeyEntry) -> Result<(), Error> {
        unimplemented!()
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        Ok(Some(semver::Version::new(3, 0, 0)))
    }

    fn query_balance(&self, _key_name: Option<String>) -> Result<Balance, Error> {
        unimplemented!()
    }

    fn query_denom_trace(&self, _hash: String) -> Result<DenomTrace, Error> {
        unimplemented!()
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        unimplemented!()
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        Ok(ChainStatus {
            height: self.context.host_height(),
            timestamp: self.context.host_timestamp(),
        })
    }

    fn query_clients(
        &self,
        _request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        unimplemented!()
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        _include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        // TODO: unclear what are the scenarios where we need to take height into account.
        let client_state = self
            .context
            .query_client_full_state(&request.client_id)
            .ok_or_else(Error::empty_response_value)?;

        let client_state = AnyClientState::from(client_state.as_ref());

        Ok((client_state, None))
    }

    fn query_upgraded_client_state(
        &self,
        _request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        unimplemented!()
    }

    fn query_connection(
        &self,
        _request: QueryConnectionRequest,
        _include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        unimplemented!()
    }

    fn query_client_connections(
        &self,
        _request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        unimplemented!()
    }

    fn query_connections(
        &self,
        _request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        unimplemented!()
    }

    fn query_connection_channels(
        &self,
        _request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        unimplemented!()
    }

    fn query_channels(
        &self,
        _request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        unimplemented!()
    }

    fn query_channel(
        &self,
        _request: QueryChannelRequest,
        _include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        unimplemented!()
    }

    fn query_channel_client_state(
        &self,
        _request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        unimplemented!()
    }

    fn query_packet_commitment(
        &self,
        _request: QueryPacketCommitmentRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        unimplemented!()
    }

    fn query_packet_commitments(
        &self,
        _request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        unimplemented!()
    }

    fn query_packet_receipt(
        &self,
        _request: QueryPacketReceiptRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        unimplemented!()
    }

    fn query_unreceived_packets(
        &self,
        _request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        unimplemented!()
    }

    fn query_packet_acknowledgement(
        &self,
        _request: QueryPacketAcknowledgementRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        unimplemented!()
    }

    fn query_packet_acknowledgements(
        &self,
        _request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        unimplemented!()
    }

    fn query_unreceived_acknowledgements(
        &self,
        _request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        unimplemented!()
    }

    fn query_next_sequence_receive(
        &self,
        _request: QueryNextSequenceReceiveRequest,
        _include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        unimplemented!()
    }

    fn query_txs(&self, _request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        unimplemented!()
    }

    fn query_packet_events(
        &self,
        _request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        unimplemented!()
    }

    fn query_host_consensus_state(
        &self,
        _request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        unimplemented!()
    }

    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        let ClientSettings::Tendermint(settings) = settings;
        let trusting_period = settings
            .trusting_period
            .unwrap_or_else(|| self.trusting_period());

        let client_state = TmClientState::new(
            self.id().clone(),
            settings.trust_threshold,
            trusting_period,
            self.trusting_period().add(Duration::from_secs(1000)),
            settings.max_clock_drift,
            height,
            ProofSpecs::default(),
            vec!["upgrade/upgradedClient".to_string()],
            AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        )
        .map_err(Error::ics07)?;

        Ok(client_state)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        Ok(Self::ConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &mut self,
        trusted_height: Height,
        target_height: Height,
        client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        let succ_trusted = self.light_client.fetch(trusted_height.increment())?;

        let Verified { target, supporting } =
            self.light_client
                .verify(trusted_height, target_height, client_state)?;

        let target_header = Self::Header {
            signed_header: target.signed_header,
            validator_set: target.validators,
            trusted_height,
            trusted_validator_set: succ_trusted.validators.clone(),
        };

        let supporting_headers = supporting
            .into_iter()
            .map(|h| Self::Header {
                signed_header: h.signed_header,
                validator_set: h.validators,
                trusted_height,
                trusted_validator_set: succ_trusted.validators.clone(),
            })
            .collect();

        Ok((target_header, supporting_headers))
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        Ok(consensus_states(&self.context, &request.client_id))
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        // IncludeProof::Yes not implemented
        assert!(matches!(include_proof, IncludeProof::No));

        let consensus_states = consensus_states(&self.context, &request.client_id);
        let consensus_state = consensus_states
            .into_iter()
            .find(|s| s.height == request.consensus_height)
            .ok_or_else(|| Error::query("Invalid consensus height".into()))?
            .consensus_state;
        Ok((consensus_state, None))
    }

    fn query_upgraded_consensus_state(
        &self,
        _request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        unimplemented!()
    }
}

pub fn consensus_states(
    ctx: &MockContext,
    client_id: &ClientId,
) -> Vec<AnyConsensusStateWithHeight> {
    ctx.ibc_store.lock().unwrap().clients[client_id]
        .consensus_states
        .iter()
        .map(|(height, cs)| {
            let consensus_state = AnyConsensusState::from(cs.as_ref());

            AnyConsensusStateWithHeight {
                height: *height,
                consensus_state,
            }
        })
        .collect()
}

// For integration tests with the modules
#[cfg(test)]
pub mod test_utils {
    use core::str::FromStr;
    use core::time::Duration;

    use ibc::core::ics24_host::identifier::ChainId;

    use crate::{
        chain::ChainType,
        config::{AddressType, ChainConfig, GasPrice, PacketFilter},
    };

    /// Returns a very minimal chain configuration, to be used in initializing `MockChain`s.
    pub fn get_basic_chain_config(id: &str) -> ChainConfig {
        ChainConfig {
            id: ChainId::from_str(id).unwrap(),
            r#type: ChainType::Mock,
            rpc_addr: "http://127.0.0.1:26656".parse().unwrap(),
            grpc_addr: "http://127.0.0.1:9090".parse().unwrap(),
            websocket_addr: "ws://127.0.0.1:26656/websocket".parse().unwrap(),
            rpc_timeout: crate::config::default::rpc_timeout(),
            account_prefix: "".to_string(),
            key_name: "".to_string(),
            store_prefix: "".to_string(),
            default_gas: None,
            key_store_type: Default::default(),
            max_gas: None,
            gas_price: GasPrice::new(0.001, "uatom".to_string()),
            gas_adjustment: None,
            gas_multiplier: None,
            fee_granter: None,
            max_msg_num: Default::default(),
            max_tx_size: Default::default(),
            clock_drift: Duration::from_secs(5),
            max_block_time: Duration::from_secs(10),
            trusting_period: Some(Duration::from_secs(14 * 24 * 60 * 60)), // 14 days
            trust_threshold: Default::default(),
            packet_filter: PacketFilter::default(),
            address_type: AddressType::default(),
            memo_prefix: Default::default(),
            proof_specs: Default::default(),
            extension_options: Default::default(),
            sequential_batch_tx: false,
        }
    }
}
