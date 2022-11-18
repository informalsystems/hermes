use alloc::string::String;
use std::sync::Mutex;
use std::{collections::HashMap, sync::Arc};
use tokio::runtime::Runtime;

use crate::relayer_mock;
use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::runtime::{MockChainRuntimeContext, MockRuntimeContext};
use crate::relayer_mock::base::types::{height::Height, packet::PacketKey, state::State};
use ibc_relayer_framework::base::one_for_all::traits::chain::OfaChainTypes;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

pub type ChainState = Arc<Mutex<HashMap<Height, State>>>;
pub type ClientId = <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::ClientId;

/// The 'state' represents the received messages and received acks at a given height.
/// The 'consensus_states' represent the known whole states of clients.
/// Usually the 'consensus_states' would be the Merkle Tree root hashes, but for
/// the MockChain the whole state is used to avoid needing to implement Merkle
/// Trees and Proofs.
pub struct MockChainContext {
    pub name: String,
    pub states: Arc<Mutex<HashMap<Height, State>>>,
    pub current_state: Arc<Mutex<(Height, State)>>,
    pub consensus_states: Arc<Mutex<HashMap<ClientId, ChainState>>>,
    pub runtime: OfaRuntimeContext<MockChainRuntimeContext<Error>>,
}

impl MockChainContext {
    pub fn new(name: String) -> Self {
        let runtime = OfaRuntimeContext::new(MockChainRuntimeContext::new(Arc::new(
            Runtime::new().unwrap(),
        )));
        let initial_state: HashMap<Height, State> =
            HashMap::from([(Height::from(1), State::default())]);
        Self {
            name,
            states: Arc::new(Mutex::new(initial_state)),
            current_state: Arc::new(Mutex::new((Height::from(1), State::default()))),
            consensus_states: Arc::new(Mutex::new(HashMap::new())),
            runtime,
        }
    }

    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn runtime(&self) -> &OfaRuntimeContext<MockRuntimeContext> {
        &self.runtime
    }

    pub fn get_latest_height(&self) -> Height {
        let current_state = self.current_state.lock().unwrap();
        current_state.0.clone()
    }

    pub fn get_current_state(&self) -> State {
        let current_state = self.current_state.lock().unwrap();
        current_state.1.clone()
    }

    // Query the chain states at all Heights
    pub fn states(&self) -> ChainState {
        self.states.clone()
    }

    pub fn update_current_state(&self, height: Height, state: State) {
        let mut current_state = self.current_state.lock().unwrap();
        *current_state = (height, state);
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
        let height = self.get_latest_height();
        let state = self.get_current_state();
        let states = self.states();
        let mut current_states = states.lock().unwrap();
        let new_height = height.increment();
        current_states.insert(new_height.clone(), state.clone());
        self.update_current_state(new_height, state);
        Ok(())
    }

    pub fn receive_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self.get_latest_height();
        let mut new_state = self.get_current_state();
        new_state.update_received(packet.port_id, packet.channel_id, packet.sequence);
        let states = self.states();
        let mut current_states = states.lock().unwrap();
        let new_height = height.increment();
        current_states.insert(new_height.clone(), new_state.clone());
        self.update_current_state(new_height, new_state);
        Ok(())
    }

    pub fn acknowledge_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self.get_latest_height();
        let mut new_state = self.get_current_state();
        new_state.update_acknowledged(packet.port_id, packet.channel_id, packet.sequence);
        let states = self.states();
        let mut current_states = states.lock().unwrap();
        let new_height = height.increment();
        current_states.insert(new_height.clone(), new_state.clone());
        self.update_current_state(new_height, new_state);
        Ok(())
    }
}
