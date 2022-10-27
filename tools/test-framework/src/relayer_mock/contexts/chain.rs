use std::collections::HashMap;

use crate::relayer_mock::base::{types::{height::Height, state::State}};

pub struct MockChainContext {
    pub state: HashMap<Height, State>,
}

impl MockChainContext {
    pub fn query_state(&self, height: Height) -> Option<&State> {
        self.state.get(&height)
    }
}

impl Default for MockChainContext {
    fn default() -> Self {
        let initial_state:HashMap<Height, State> = HashMap::from([
            (Height::from(1), State::default()),
        ]);
        Self { state: initial_state }
    }
}