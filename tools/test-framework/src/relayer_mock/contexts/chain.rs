#![allow(dead_code)]
use std::collections::HashMap;
use std::sync::Arc;

use std::sync::Mutex;

use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use tokio::runtime::Runtime;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::height::Height;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::state::State;

pub struct MockChainContext {
    pub name: String,
    pub state: Arc<Mutex<HashMap<Height, State>>>,
    pub runtime: OfaRuntimeContext<TokioRuntimeContext<Error>>,
}

impl MockChainContext {
    fn new(name: String, runtime: OfaRuntimeContext<TokioRuntimeContext<Error>>) -> Self {
        Self {
            name,
            state: Arc::new(Mutex::new(HashMap::new())),
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
        let state = self.state.lock().unwrap();
        state.keys().into_iter().max().cloned()
    }

    pub fn query_state(&self, height: Height) -> Option<State> {
        let state = self.state.lock().unwrap();
        state.get(&height).cloned()
    }

    pub fn receive_packet(&self, packet: PacketKey) {
        if let Some(height) = self.get_latest_height() {
            if let Some(state) = self.query_state(height.clone()) {
                let mut new_state = state;
                let event = format!(
                    "{}/{}/{}",
                    packet.channel_id, packet.port_id, packet.sequence
                );
                new_state.update_received(event);
                let mut state = self.state.lock().unwrap();
                state.insert(height.increment(), new_state);
            }
        }
    }

    pub fn acknowledge_packet(&self, packet: PacketKey) {
        if let Some(height) = self.get_latest_height() {
            if let Some(state) = self.query_state(height.clone()) {
                let mut new_state = state;
                let event = format!(
                    "{}/{}/{}",
                    packet.channel_id, packet.port_id, packet.sequence
                );
                new_state.update_acknowledged(event);
                let mut state = self.state.lock().unwrap();
                state.insert(height.increment(), new_state);
            }
        }
    }
}

impl Default for MockChainContext {
    fn default() -> Self {
        let runtime =
            OfaRuntimeContext::new(TokioRuntimeContext::new(Arc::new(Runtime::new().unwrap())));
        let initial_state: HashMap<Height, State> =
            HashMap::from([(Height::from(1), State::default())]);
        Self {
            name: "default".to_owned(),
            state: Arc::new(Mutex::new(initial_state)),
            runtime,
        }
    }
}
