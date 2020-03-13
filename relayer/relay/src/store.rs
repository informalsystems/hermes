use tendermint::lite::{Height, TrustedState};

use crate::chain::Chain;
use crate::error;

pub mod mem;

pub enum StoreHeight {
    Last,
    Given(Height),
}

pub trait Store<C>
where
    C: Chain,
{
    fn last_height(&self) -> Option<Height>;

    fn add(&mut self, state: TrustedState<C::Commit, C::Header>) -> Result<(), error::Error>;

    fn get(&self, height: StoreHeight)
        -> Result<&TrustedState<C::Commit, C::Header>, error::Error>;

    fn has(&self, height: StoreHeight) -> bool {
        self.get(height).is_ok()
    }
}
