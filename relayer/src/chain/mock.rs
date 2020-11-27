use std::sync::{Arc, Mutex};

use crossbeam_channel as channel;
use prost_types::Any;
use tendermint::account::Id;
use tendermint_light_client::supervisor::Supervisor;
use tendermint_testgen::light_block::TMLightBlock;
use tokio::runtime::Runtime;

use ibc::ics07_tendermint::client_state::ClientState as TendermintClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
use ibc::ics18_relayer::context::ICS18Context;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics23_commitment::merkle::MerkleProof;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics24_host::Path;
use ibc::mock::context::MockContext;
use ibc::mock::host::HostType;
use ibc::Height;

use crate::chain::{Chain, QueryResponse};
use crate::config::ChainConfig;
use crate::error::Error;
use crate::event::monitor::{EventBatch, EventMonitor};
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::light_client::{mock::LightClient as MockLightClient, LightClient};

/// The representation of a mocked chain as the relayer sees it.
/// The relayer runtime and the light client will engage with the MockChain to query/send tx.
pub struct MockChain {
    pub context: MockContext,
    pub config: ChainConfig,
}

#[allow(unused_variables)]
impl Chain for MockChain {
    type LightBlock = TMLightBlock;
    type Header = TendermintHeader;
    type ConsensusState = TendermintConsensusState;
    type ClientState = TendermintClientState;

    fn bootstrap(config: ChainConfig, _rt: Arc<Mutex<Runtime>>) -> Result<Self, Error> {
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
    fn init_light_client(&self) -> Result<(Box<dyn LightClient<Self>>, Option<Supervisor>), Error> {
        let light_client = MockLightClient::new();

        Ok((Box::new(light_client), None))
    }

    fn init_event_monitor(
        &self,
        rt: Arc<Mutex<Runtime>>,
    ) -> Result<(Option<EventMonitor>, channel::Receiver<EventBatch>), Error> {
        let (_, rx) = channel::unbounded();
        Ok((None, rx))
    }

    fn id(&self) -> &ChainId {
        &self.config.id
    }

    fn keybase(&self) -> &KeyRing {
        unimplemented!()
    }

    fn query(&self, data: Path, height: Height, prove: bool) -> Result<QueryResponse, Error> {
        unimplemented!()
    }

    fn send_tx(&self, proto_msgs: Vec<Any>) -> Result<String, Error> {
        unimplemented!()
    }

    fn get_signer(&mut self) -> Result<Id, Error> {
        unimplemented!()
    }

    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        unimplemented!()
    }

    fn build_client_state(&self, height: Height) -> Result<Self::ClientState, Error> {
        unimplemented!()
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        unimplemented!()
    }

    fn build_header(
        &self,
        trusted_light_block: Self::LightBlock,
        target_light_block: Self::LightBlock,
    ) -> Result<Self::Header, Error> {
        unimplemented!()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        Ok(self.context.query_latest_height())
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Self::ClientState, Error> {
        unimplemented!()
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        unimplemented!()
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        unimplemented!()
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        unimplemented!()
    }
}

// For integration tests with the modules
#[cfg(test)]
pub mod test_utils {
    use std::str::FromStr;

    use ibc::ics24_host::identifier::ChainId;

    use crate::config::ChainConfig;

    pub fn get_basic_chain_config(id: &str) -> ChainConfig {
        ChainConfig {
            id: ChainId::from_str(id).unwrap(),
            rpc_addr: "35.192.61.41:26656".parse().unwrap(),
            grpc_addr: "".to_string(),
            account_prefix: "".to_string(),
            key_name: "".to_string(),
            store_prefix: "".to_string(),
            client_ids: vec![],
            gas: 0,
            clock_drift: Default::default(),
            trusting_period: Default::default(),
            trust_threshold: Default::default(),
            peers: None,
        }
    }
}
