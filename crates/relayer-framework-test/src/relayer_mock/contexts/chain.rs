use alloc::string::String;
use std::collections::hash_map::Entry;
use std::sync::Mutex;
use std::{collections::HashMap, sync::Arc};
use tokio::runtime::Runtime;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::{
    ChainState, ChainStatus, ChannelId, ClientId, PortId, Sequence,
};
use crate::relayer_mock::base::types::chain::MockChainStatus;
use crate::relayer_mock::base::types::runtime::{MockChainRuntimeContext, MockRuntimeContext};
use crate::relayer_mock::base::types::{height::Height, packet::PacketKey, state::State};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

/// The `consensus_states` represents the ConsensusState described in ICS002, at all heights.
/// The `consensus_state` represents the ConsensusState described in ICS002, at the latest height.
/// The `client_states` represents the ClientState described in ICS002, for all the known clients.
///
/// Usually the 'ClientState' would use the root hashes of a Merle Tree, but since the MockChain
/// is used for testing and will have a small number of states, the whole state is used. The reason
/// is to avoid needing to implement Merkle Trees and Proofs.
pub struct MockChainContext {
    pub name: String,
    pub consensus_states: Arc<Mutex<HashMap<Height, State>>>,
    pub consensus_state: Arc<Mutex<ChainStatus>>,
    pub client_states: Arc<Mutex<HashMap<ClientId, HashMap<Height, ChainState>>>>,
    pub runtime: OfaRuntimeContext<MockChainRuntimeContext<Error>>,
    pub sequence: Arc<Mutex<Sequence>>,
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
            consensus_states: Arc::new(Mutex::new(initial_state)),
            consensus_state: Arc::new(Mutex::new(MockChainStatus::new(
                Height::from(1),
                Height::from(1),
                State::default(),
            ))),
            client_states: Arc::new(Mutex::new(HashMap::new())),
            runtime,
            sequence: Arc::new(Mutex::new(1)),
        }
    }

    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn runtime(&self) -> &OfaRuntimeContext<MockRuntimeContext> {
        &self.runtime
    }

    pub fn get_latest_height(&self) -> Height {
        let consensus_state = self.consensus_state.lock().unwrap();
        consensus_state.height.clone()
    }

    pub fn get_current_state(&self) -> MockChainStatus {
        let consensus_state = self.consensus_state.lock().unwrap();
        consensus_state.clone()
    }

    pub fn consensus_states(&self) -> ChainState {
        self.consensus_states.clone()
    }

    fn get_and_increment_sequence(&self) -> Sequence {
        let mut sequence = self.sequence.lock().unwrap();
        let old_sequence = *sequence;
        *sequence = old_sequence + 1;
        old_sequence
    }

    pub fn update_current_state(&self, height: Height, state: State) {
        let mut locked_consensus_state = self.consensus_state.lock().unwrap();
        *locked_consensus_state = MockChainStatus::new(height.clone(), height, state);
    }

    // Query the chain state at a given Height. This is used to see which receive and
    // acknowledgment messages have been processed by the Mock Chain
    pub fn query_state_at_height(&self, height: Height) -> Option<State> {
        let locked_consensus_state = self.consensus_states.lock().unwrap();
        locked_consensus_state.get(&height).cloned()
    }

    /// Query the consensus state of a Client at a given height.
    /// Refer to the `queryConsensusState` of ICS002.
    pub fn query_consensus_state_at_height(
        &self,
        client_id: ClientId,
        height: Height,
    ) -> Result<ChainState, Error> {
        let client_states = self.client_states.lock().unwrap();
        let client_consensus_states = client_states
            .get(&client_id)
            .ok_or_else(|| Error::no_consensus_state(client_id.clone()))?;
        let client_consensus_state = client_consensus_states
            .get(&height)
            .ok_or_else(|| Error::no_consensus_state_at_height(client_id, height.0))?;
        Ok(client_consensus_state.clone())
    }

    /// Insert a new Consensus State for a given Client at a given Height.
    /// If there already is a Consensus State for the Client at the given Height, which is different
    /// from the given State, return an error as a Chain is not allowed to have two different Consensus
    /// States at the same Height.
    /// This is used for the `updateClient` of ICS002, with the misbehaviour being when trying to update
    /// an already existing Consensus State with a different value.
    pub fn insert_consensus_state(
        &self,
        client_id: String,
        height: Height,
        state: ChainState,
    ) -> Result<(), Error> {
        let mut client_states = self.client_states.lock().unwrap();
        let client_consensus_states = match client_states.get(&client_id) {
            Some(client_consensus_states) => {
                let mut client_consensus_states = client_consensus_states.clone();
                match client_consensus_states.entry(height.clone()) {
                    Entry::Occupied(o) => {
                        // Check if the existing Consensus State at the given height differs
                        // from the one passed.
                        return is_chain_state_equal(o.get().clone(), state);
                    }
                    Entry::Vacant(_) => client_consensus_states.insert(height, state),
                };
                client_consensus_states
            }
            // If the Client doesn't have any Consensus State, create one with the given
            // state as initial Consensus State.
            None => HashMap::from([(height, state)]),
        };
        // Update the Client States of the Chain.
        client_states.insert(client_id, client_consensus_states);

        Ok(())
    }

    /// Adding a new empty Block to the MockChain simply advances the Height by 1
    /// while keeping the same Consensus State.
    /// This can be used to manually advance the Height of a MockChain by 1.
    pub fn new_block(&self) -> Result<(), Error> {
        let height = self.get_latest_height();
        let state = self.get_current_state().state;
        let states = self.consensus_states();
        let mut current_states = states.lock().unwrap();
        let new_height = height.increment();
        current_states.insert(new_height.clone(), state.clone());
        self.update_current_state(new_height, state);
        Ok(())
    }

    /// Receiving a packet adds a new Consensus State with the received packet information
    /// at a Height + 1.
    pub fn send_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self.get_latest_height();

        // Retrieve the current state and update it with the newly received packet
        let mut new_state = self.get_current_state().state;
        new_state.update_sent(packet.port_id, packet.channel_id, packet.sequence);

        // Add the new state to the Consensus States of the Chain at a Height + 1
        let consensus_states = self.consensus_states();
        let mut locked_consensus_states = consensus_states.lock().unwrap();
        let new_height = height.increment();
        locked_consensus_states.insert(new_height.clone(), new_state.clone());

        // Update the current state of the Chain
        self.update_current_state(new_height, new_state);

        Ok(())
    }

    /// Receiving a packet adds a new Consensus State with the received packet information
    /// at a Height + 1.
    pub fn receive_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self.get_latest_height();

        // Retrieve the current state and update it with the newly received packet
        let mut new_state = self.get_current_state().state;
        new_state.update_received(packet.port_id, packet.channel_id, packet.sequence);

        // Add the new state to the Consensus States of the Chain at a Height + 1
        let consensus_states = self.consensus_states();
        let mut locked_consensus_states = consensus_states.lock().unwrap();
        let new_height = height.increment();
        locked_consensus_states.insert(new_height.clone(), new_state.clone());

        // Update the current state of the Chain
        self.update_current_state(new_height, new_state);

        Ok(())
    }

    /// Receiving an acknowledgement adds a new Consensus State with the received acknowledgement
    /// information at a Height + 1.
    pub fn acknowledge_packet(&self, packet: PacketKey) -> Result<(), Error> {
        let height = self.get_latest_height();

        // Retrieve the current state and update it with the newly received acknowledgement
        let mut new_state = self.get_current_state().state;
        new_state.update_acknowledged(packet.port_id, packet.channel_id, packet.sequence);

        // Add the new state to the Consensus States of the Chain at a Height + 1
        let consensus_states = self.consensus_states();
        let mut locked_consensus_states = consensus_states.lock().unwrap();
        let new_height = height.increment();
        locked_consensus_states.insert(new_height.clone(), new_state.clone());

        // Update the current state of the Chain
        self.update_current_state(new_height, new_state);

        Ok(())
    }

    pub fn build_send_packet(
        &self,
        client_id: ClientId,
        channel_id: ChannelId,
        port_id: PortId,
        timeout_height: Height,
        timeout_timestamp: Height,
    ) -> PacketKey {
        let sequence = self.get_and_increment_sequence();
        PacketKey::new(
            client_id,
            channel_id,
            port_id,
            sequence,
            timeout_height,
            timeout_timestamp,
        )
    }
}

fn is_chain_state_equal(state1: ChainState, state2: ChainState) -> Result<(), Error> {
    let s1 = state1.lock().unwrap();
    let s2 = state2.lock().unwrap();
    if *s1 != *s2 {
        return Err(Error::consensus_duplicate());
    }
    Ok(())
}
