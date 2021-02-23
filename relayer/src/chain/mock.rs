use std::ops::Add;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use crossbeam_channel as channel;
use prost_types::Any;
use tendermint::account::Id;
use tendermint_testgen::light_block::TMLightBlock;
use tokio::runtime::Runtime;

use ibc::downcast;
use ibc::events::IbcEvent;
use ibc::ics02_client::client_def::AnyClientState;
use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics04_channel::channel::{ChannelEnd, QueryPacketEventDataRequest};
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics07_tendermint::client_state::ClientState as TendermintClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
use ibc::ics18_relayer::context::Ics18Context;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::mock::context::MockContext;
use ibc::mock::host::HostType;
use ibc::test_utils::get_dummy_account_id;
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryChannelsRequest, QueryConnectionChannelsRequest,
    QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::ibc::core::connection::v1::{
    QueryClientConnectionsRequest, QueryConnectionsRequest,
};

use crate::chain::Chain;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::event::monitor::EventBatch;
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::light_client::{mock::LightClient as MockLightClient, LightClient};

/// The representation of a mocked chain as the relayer sees it.
/// The relayer runtime and the light client will engage with the MockChain to query/send tx; the
/// primary interface for doing so is captured by `ICS18Context` which this struct can access via
/// the `context` field.
pub struct MockChain {
    config: ChainConfig,
    context: MockContext,
}

impl Chain for MockChain {
    type LightBlock = TMLightBlock;
    type Header = TendermintHeader;
    type ConsensusState = TendermintConsensusState;
    type ClientState = TendermintClientState;

    fn bootstrap(config: ChainConfig, _rt: Arc<Runtime>) -> Result<Self, Error> {
        Ok(MockChain {
            config: config.clone(),
            context: MockContext::new(
                config.id.clone(),
                HostType::SyntheticTendermint,
                50,
                Height::new(config.id.version(), 20),
            ),
        })
    }

    #[allow(clippy::type_complexity)]
    fn init_light_client(
        &self,
    ) -> Result<(Box<dyn LightClient<Self>>, Option<thread::JoinHandle<()>>), Error> {
        let light_client = MockLightClient::new(self);

        Ok((Box::new(light_client), None))
    }

    fn init_event_monitor(
        &self,
        _rt: Arc<Runtime>,
    ) -> Result<
        (
            channel::Receiver<EventBatch>,
            Option<thread::JoinHandle<()>>,
        ),
        Error,
    > {
        let (_, rx) = channel::unbounded();
        Ok((rx, None))
    }

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn keybase(&self) -> &KeyRing {
        unimplemented!()
    }

    fn send_msgs(&mut self, proto_msgs: Vec<Any>) -> Result<Vec<IbcEvent>, Error> {
        // Use the ICS18Context interface to submit the set of messages.
        let events = self
            .context
            .send(proto_msgs)
            .map_err(|e| Kind::Rpc(self.config.rpc_addr.clone()).context(e))?;

        Ok(events)
    }

    fn get_signer(&mut self) -> Result<Id, Error> {
        Ok(get_dummy_account_id())
    }

    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        unimplemented!()
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        unimplemented!()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        Ok(self.context.query_latest_height())
    }

    fn query_clients(&self, _request: QueryClientStatesRequest) -> Result<Vec<ClientId>, Error> {
        unimplemented!()
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        _height: Height,
    ) -> Result<Self::ClientState, Error> {
        // TODO: unclear what are the scenarios where we need to take height into account.
        let any_state = self
            .context
            .query_client_full_state(client_id)
            .ok_or(Kind::EmptyResponseValue)?;
        let client_state = downcast!(any_state => AnyClientState::Tendermint).ok_or_else(|| {
            Kind::Query("client state".into()).context("unexpected client state type")
        })?;
        Ok(client_state)
    }

    fn query_connection(
        &self,
        _connection_id: &ConnectionId,
        _height: Height,
    ) -> Result<ConnectionEnd, Error> {
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
    ) -> Result<Vec<ConnectionId>, Error> {
        unimplemented!()
    }

    fn query_connection_channels(
        &self,
        _request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<ChannelId>, Error> {
        unimplemented!()
    }

    fn query_channels(&self, _request: QueryChannelsRequest) -> Result<Vec<ChannelId>, Error> {
        unimplemented!()
    }

    fn query_channel(
        &self,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _height: Height,
    ) -> Result<ChannelEnd, Error> {
        unimplemented!()
    }

    fn query_packet_commitments(
        &self,
        _request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        unimplemented!()
    }

    fn query_unreceived_packets(
        &self,
        _request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        unimplemented!()
    }

    fn query_packet_acknowledgements(
        &self,
        _request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        unimplemented!()
    }

    fn query_unreceived_acknowledgements(
        &self,
        _request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        unimplemented!()
    }

    fn query_next_sequence_receive(
        &self,
        _request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error> {
        unimplemented!()
    }

    fn query_txs(&self, _request: QueryPacketEventDataRequest) -> Result<Vec<IbcEvent>, Error> {
        unimplemented!()
    }

    fn proven_client_state(
        &self,
        _client_id: &ClientId,
        _height: Height,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        unimplemented!()
    }

    fn proven_connection(
        &self,
        _connection_id: &ConnectionId,
        _height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        unimplemented!()
    }

    fn proven_client_consensus(
        &self,
        _client_id: &ClientId,
        _consensus_height: Height,
        _height: Height,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        unimplemented!()
    }

    fn proven_channel(
        &self,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _height: Height,
    ) -> Result<(ChannelEnd, MerkleProof), Error> {
        unimplemented!()
    }

    fn proven_packet(
        &self,
        _packet_type: PacketMsgType,
        _port_id: PortId,
        _channel_id: ChannelId,
        _sequence: Sequence,
        _height: Height,
    ) -> Result<(Vec<u8>, MerkleProof), Error> {
        unimplemented!()
    }

    fn build_client_state(&self, height: Height) -> Result<Self::ClientState, Error> {
        let client_state = Self::ClientState::new(
            self.id().clone(),
            self.config.trust_threshold,
            self.config.trusting_period,
            self.config.trusting_period.add(Duration::from_secs(1000)),
            Duration::from_millis(3000),
            height,
            Height::zero(),
            vec!["upgrade/upgradedClient".to_string()],
            false,
            false,
        )
        .map_err(|e| Kind::BuildClientStateFailure.context(e))?;

        Ok(client_state)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        Ok(Self::ConsensusState::from(light_block.signed_header.header))
    }

    fn build_header(
        &self,
        trusted_light_block: Self::LightBlock,
        target_light_block: Self::LightBlock,
    ) -> Result<Self::Header, Error> {
        Ok(Self::Header {
            signed_header: target_light_block.signed_header.clone(),
            validator_set: target_light_block.validators,
            trusted_height: Height::new(
                self.id().version(),
                u64::from(trusted_light_block.signed_header.header.height),
            ),
            trusted_validator_set: trusted_light_block.validators,
        })
    }
}

// For integration tests with the modules
#[cfg(test)]
pub mod test_utils {
    use std::str::FromStr;
    use std::time::Duration;

    use ibc::ics24_host::identifier::ChainId;

    use crate::config::ChainConfig;

    /// Returns a very minimal chain configuration, to be used in initializing `MockChain`s.
    pub fn get_basic_chain_config(id: &str) -> ChainConfig {
        ChainConfig {
            id: ChainId::from_str(id).unwrap(),
            rpc_addr: "127.0.0.1:26656".parse().unwrap(),
            grpc_addr: "".to_string(),
            account_prefix: "".to_string(),
            key_name: "".to_string(),
            store_prefix: "".to_string(),
            gas: None,
            max_msg_num: None,
            max_tx_size: None,
            clock_drift: Duration::from_secs(5),
            trusting_period: Duration::from_secs(14 * 24 * 60 * 60), // 14 days
            trust_threshold: Default::default(),
            peers: None,
        }
    }
}
