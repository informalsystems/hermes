use std::collections::HashMap;

use anomaly::fail;
use tendermint::lite::{types::Header, Height, TrustedState};

use super::{Store, StoreHeight};

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;

/// Transient in-memory store
pub struct MemStore<C: Chain> {
    last_height: Height,
    trust_options: Option<TrustOptions>,
    store: HashMap<Height, TrustedState<C::Commit, C::Header>>,
}

impl<C: Chain> MemStore<C> {
    pub fn new() -> Self {
        Self {
            last_height: 0,
            trust_options: None,
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
    fn last_height(&self) -> Result<Option<Height>, error::Error> {
        if self.last_height == 0 {
            Ok(None)
        } else {
            Ok(Some(self.last_height))
        }
    }

    fn add(&mut self, state: TrustedState<C::Commit, C::Header>) -> Result<(), error::Error> {
        let height = state.last_header().header().height();

        self.last_height = height;
        self.store.insert(height, state);

        Ok(())
    }

    fn get(&self, height: StoreHeight) -> Result<TrustedState<C::Commit, C::Header>, error::Error> {
        let height = match height {
            StoreHeight::Last => self.last_height()?.unwrap_or(0),
            StoreHeight::Given(height) => height,
        };

        match self.store.get(&height) {
            Some(state) => Ok(state.clone()),
            None => fail!(
                error::Kind::Store,
                "could not load height {} from store",
                height
            ),
        }
    }

    fn get_trust_options(&self) -> Result<TrustOptions, error::Error> {
        match self.trust_options {
            Some(ref trust_options) => Ok(trust_options.clone()),
            None => fail!(error::Kind::Store, "no trust options in trusted store"),
        }
    }

    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error> {
        self.trust_options = Some(trust_options);
        Ok(())
    }
}
