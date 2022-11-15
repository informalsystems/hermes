use alloc::string::{String, ToString};
use std::sync::Mutex;
use std::{collections::HashMap, sync::Arc};
use tokio::runtime::Runtime;

use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::tests;
use crate::tests::relayer_mock::base::error::Error;
use crate::tests::relayer_mock::base::types::{height::Height, packet::PacketKey, state::State};

pub type ChainState = Arc<Mutex<HashMap<Height, State>>>;
pub type ClientId =
    <tests::relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::ClientId;

/// The 'state' represents the received messages and received acks at a given height.
/// The 'consensus_states' represent the known whole states of clients.
/// Usually the 'consensus_states' would be the Merkle Tree root hashes, but for
/// the MockChain the whole state is used to avoid needing to implement Merkle
/// Trees and Proofs.
pub struct MockChainContext {
    pub name: String,
    pub states: Arc<Mutex<HashMap<Height, State>>>,
    pub consensus_states: Arc<Mutex<HashMap<ClientId, ChainState>>>,
    pub runtime: OfaRuntimeContext<TokioRuntimeContext<Error>>,
}

impl MockChainContext {
    pub fn new(name: String) -> Self {
        let runtime =
            OfaRuntimeContext::new(TokioRuntimeContext::new(Arc::new(Runtime::new().unwrap())));
        let initial_state: HashMap<Height, State> =
            HashMap::from([(Height::from(1), State::default())]);
        Self {
            name,
            states: Arc::new(Mutex::new(initial_state)),
            consensus_states: Arc::new(Mutex::new(HashMap::new())),
            runtime,
        }
    }

    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn runtime(&self) -> &OfaRuntimeContext<TokioRuntimeContext<Error>> {
        &self.runtime
    }

    pub fn get_latest_height(&self) -> Option<Height> {
        let state = self.states.lock().unwrap();
        state.keys().into_iter().max().cloned()
    }

    // Query the chain states at all Heights
    pub fn state(&self) -> ChainState {
        self.states.clone()
    }

    // Query the chain state at a given Height. This is used to see which receive and
    // acknowledgment messages have been processed by the Mock Chain
    pub fn query_state_at_height(&self, height: Height) -> Option<State> {
        let states = self.states.lock().unwrap();
        states.get(&height).cloned()
    }

    // Query the consensus state of a Client, which is used to see if an update client
    // message must be sent.
    pub fn query_consensus_state(&self, client_id: ClientId) -> Option<ChainState> {
        let consensus_states = self.consensus_states.lock().unwrap();
        consensus_states.get(&client_id).cloned()
    }

    pub fn insert_consensus_state(&self, client_id: String, state: ChainState) {
        let mut consensus_states = self.consensus_states.lock().unwrap();
        consensus_states.insert(client_id, state);
    }

    pub fn new_block(&self) -> Result<(), Error> {
        let height = self
            .get_latest_height()
            .ok_or_else(|| Error::no_height(self.name().to_string()))?;
        let current_state = self
            .query_state_at_height(height.clone())
            .ok_or_else(|| Error::no_height_state(height.0))?;
        let mut state = self.states.lock().unwrap();
        state.insert(height.increment(), current_state);
        Ok(())
    }

    pub fn receive_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self
            .get_latest_height()
            .ok_or_else(|| Error::no_height(self.name().to_string()))?;
        let mut new_state = self
            .query_state_at_height(height.clone())
            .ok_or_else(|| Error::no_height_state(height.0))?;
        new_state.update_received(packet.port_id, packet.channel_id, packet.sequence);
        let mut state = self.states.lock().unwrap();
        state.insert(height.increment(), new_state);
        Ok(())
    }

    pub fn acknowledge_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self
            .get_latest_height()
            .ok_or_else(|| Error::no_height(self.name().to_string()))?;
        let mut new_state = self
            .query_state_at_height(height.clone())
            .ok_or_else(|| Error::no_height_state(height.0))?;
        new_state.update_acknowledged(packet.port_id, packet.channel_id, packet.sequence);
        let mut state = self.states.lock().unwrap();
        state.insert(height.increment(), new_state);
        Ok(())
    }
}
