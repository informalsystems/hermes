//! The MockChainContext uses a ChainState alias for it's consensus_state.
//! This type is a HashMap<Height, State>, used to represent the State of
//! the chain at all Heights.
//! The consensus_states is a HashMap<Height, ChainState> used to send the
//! consensus_state of the chain at a specific Height inside a client upgrade
//! message.
//! The client_states is a HashMap<ClientId, HashMap<Height, ChainState>>.
//! This is used to check the consensus_state for a specific client, at a
//! specific height.
//! Usually the client_states would use the root hashes of a Merle Tree,
//! but since the MockChain is used for testing and will have a small number
//! of states, the whole state is used. This avoids needing to implement
//! Merkle Trees and Proofs.

use alloc::string::String;
use std::collections::hash_map::Entry;
use std::sync::Mutex;
use std::{collections::HashMap, sync::Arc};

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::{
    ChainState, ChannelId, ClientId, ConsensusState, PortId, Sequence,
};
use crate::relayer_mock::base::types::runtime::{MockChainRuntimeContext, MockRuntimeContext};
use crate::relayer_mock::base::types::{
    height::Height as MockHeight, packet::PacketKey, state::State,
};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

pub struct MockChainContext {
    pub name: String,
    pub consensus_states: Arc<Mutex<HashMap<MockHeight, ChainState>>>,
    pub consensus_state: Arc<Mutex<ChainState>>,
    pub client_states: Arc<Mutex<HashMap<ClientId, HashMap<MockHeight, ChainState>>>>,
    pub runtime: OfaRuntimeContext<MockChainRuntimeContext<Error>>,
    pub sequence: Arc<Mutex<Sequence>>,
}

impl MockChainContext {
    pub fn new(name: String) -> Self {
        let runtime = OfaRuntimeContext::new(MockChainRuntimeContext::new());
        let chain_state: HashMap<MockHeight, ConsensusState> =
            HashMap::from([(MockHeight::from(1), State::default())]);
        let initial_state: HashMap<MockHeight, ChainState> =
            HashMap::from([(MockHeight::from(1), chain_state.clone())]);
        Self {
            name,
            consensus_states: Arc::new(Mutex::new(initial_state)),
            consensus_state: Arc::new(Mutex::new(chain_state)),
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

    /// The MockChain has one and only one State at every height, so this method must return a MockHeight.
    pub fn get_latest_height(&self) -> MockHeight {
        let consensus_state = self.consensus_state.lock().unwrap();
        consensus_state.keys().max().unwrap().clone()
    }

    /// Get the current state of the chain, which is the State at the latest height.
    /// The MockChain has one and only one State at every height, so this method must return a State.
    pub fn get_current_state(&self) -> State {
        let height = self.get_latest_height();
        let locked_consensus_state = self.consensus_state.lock().unwrap();
        let state = locked_consensus_state.get(&height).unwrap();
        state.clone()
    }

    /// Query the chain state at a given Height. This is used to see which receive and
    /// acknowledgment messages have been processed by the Mock Chain.
    /// The MockChain has one and only one State at every height, so this method must return a ChainState.
    pub fn query_state_at_height(&self, height: MockHeight) -> ChainState {
        let locked_consensus_state = self.consensus_states.lock().unwrap();
        let state = locked_consensus_state.get(&height).unwrap();
        state.clone()
    }

    /// Query the consensus state of a Client at a given height.
    /// Refer to the `queryConsensusState` of ICS002.
    pub fn query_client_state_at_height(
        &self,
        client_id: ClientId,
        height: MockHeight,
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
    pub fn insert_client_state(
        &self,
        client_id: String,
        height: MockHeight,
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
                        if o.get().clone() != state {
                            return Err(Error::consensus_divergence());
                        }
                    }
                    Entry::Vacant(_) => {
                        client_consensus_states.insert(height, state);
                    }
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

    /// Insert the current state at Height + 1. This is used to advance the chain's Height by 1
    /// without changing its state.
    pub fn new_block(&self) -> Result<(), Error> {
        // Retrieve the current state
        let current_state = self.get_current_state();

        // Update the Consensus States of the Chain, which will increase the Height by 1.
        self.update_current_state(current_state)?;

        Ok(())
    }

    /// Sending a packet adds a new Consensus State with the sent packet information
    /// at a Height + 1.
    pub fn send_packet(&self, packet: PacketKey) -> Result<(), Error> {
        // Retrieve the current state and update it with the newly sent packet
        let mut new_state = self.get_current_state();
        new_state.update_sent(packet.port_id, packet.channel_id, packet.sequence);

        // Update the Consensus States of the Chain
        self.update_current_state(new_state)?;

        Ok(())
    }

    /// Receiving a packet adds a new Consensus State with the received packet information
    /// at a Height + 1.
    pub fn receive_packet(&self, packet: PacketKey) -> Result<(), Error> {
        // Retrieve the current state and update it with the newly received packet
        let mut new_state = self.get_current_state();
        new_state.update_received(packet.port_id, packet.channel_id, packet.sequence);

        // Update the current state of the Chain
        self.update_current_state(new_state)?;

        Ok(())
    }

    /// Receiving an acknowledgement adds a new Consensus State with the received acknowledgement
    /// information at a Height + 1.
    pub fn acknowledge_packet(&self, packet: PacketKey) -> Result<(), Error> {
        // Retrieve the current state and update it with the newly received acknowledgement
        let mut new_state = self.get_current_state();
        new_state.update_acknowledged(packet.port_id, packet.channel_id, packet.sequence);

        // Update the current state of the Chain
        self.update_current_state(new_state)?;

        Ok(())
    }

    /// Build a packet using the chain's Sequence information.
    pub fn build_send_packet(
        &self,
        client_id: ClientId,
        channel_id: ChannelId,
        port_id: PortId,
        timeout_height: MockHeight,
        timeout_timestamp: MockHeight,
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

    /// Get the Sequence value used for sending a packet and increment the value.
    fn get_and_increment_sequence(&self) -> Sequence {
        let mut sequence = self.sequence.lock().unwrap();
        let old_sequence = *sequence;
        *sequence = old_sequence + 1;
        old_sequence
    }

    /// Update the chain's Consensus State and Consensus States at the same time to insure
    /// they are always synchronized.
    /// The MockChain must have a one and only one State at every height.
    fn update_current_state(&self, state: State) -> Result<(), Error> {
        let latest_height = self.get_latest_height();
        let new_height = latest_height.increment();
        let mut locked_consensus_state = self.consensus_state.lock().unwrap();
        locked_consensus_state.insert(new_height.clone(), state);
        let mut locked_consensus_states = self.consensus_states.lock().unwrap();
        locked_consensus_states.insert(new_height, locked_consensus_state.clone());
        Ok(())
    }
}
