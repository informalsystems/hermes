use std::collections::HashMap;

use anomaly::fail;
use tendermint::lite::{types::Header, Height, TrustedState};

use super::{Store, StoreHeight};
use crate::chain::Chain;
use crate::error;

pub struct MemStore<C: Chain> {
    last_height: Height,
    store: HashMap<Height, TrustedState<C::Commit, C::Header>>,
}

impl<C: Chain> MemStore<C> {
    pub fn new() -> Self {
        Self {
            last_height: 0,
            store: Default::default(),
        }
    }
}

impl<C: Chain> Default for MemStore<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: Chain> Store<C> for MemStore<C> {
    fn last_height(&self) -> Option<Height> {
        if self.last_height == 0 {
            None
        } else {
            Some(self.last_height)
        }
    }

    fn add(&mut self, state: TrustedState<C::Commit, C::Header>) -> Result<(), error::Error> {
        let height = state.last_header().header().height();

        self.last_height = height;
        self.store.insert(height, state);

        Ok(())
    }

    fn get(
        &self,
        height: StoreHeight,
    ) -> Result<&TrustedState<C::Commit, C::Header>, error::Error> {
        let height = match height {
            StoreHeight::Last => self.last_height,
            StoreHeight::Given(height) => height,
        };

        match self.store.get(&height) {
            Some(state) => Ok(state),
            None => fail!(
                error::Kind::Store,
                "could not load height {} from store",
                height
            ),
        }
    }
}
