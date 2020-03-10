use std::collections::HashMap;

use anomaly::fail;
use tendermint::lite::{types::Header, Height, TrustedState};

use super::Store;
use crate::chain::Chain;
use crate::error;

pub struct MemStore<C>
where
    C: Chain,
{
    height: Height,
    store: HashMap<Height, TrustedState<C::Commit, C::Header>>,
}

impl<C> Store<C> for MemStore<C>
where
    C: Chain,
{
    fn height(&self) -> Height {
        self.height
    }

    fn add(&mut self, state: TrustedState<C::Commit, C::Header>) -> Result<(), error::Error> {
        let height = state.last_header().header().height();

        self.height = height;
        self.store.insert(height, state);

        Ok(())
    }

    fn get(&self, height: Height) -> Result<&TrustedState<C::Commit, C::Header>, error::Error> {
        let mut h = height;

        if h == 0 {
            h = self.height
        }

        match self.store.get(&h) {
            Some(state) => Ok(state),
            None => fail!(
                error::Kind::LiteClient,
                "could not load height {} from store",
                h
            ),
        }
    }
}
