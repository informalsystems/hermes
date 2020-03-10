use std::collections::HashMap;

use anomaly::fail;
use tendermint::lite::{types::Header, Height, TrustedState};

use super::{Store, StoreHeight};
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

    fn get(
        &self,
        height: StoreHeight,
    ) -> Result<&TrustedState<C::Commit, C::Header>, error::Error> {
        let height = match height {
            StoreHeight::Current => self.height,
            StoreHeight::GivenHeight(height) => height,
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
