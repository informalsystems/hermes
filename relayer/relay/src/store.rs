use tendermint::lite::{Height, TrustedState};

use crate::chain::Chain;
use crate::error;

pub mod mem;

pub trait Store<C>
where
    C: Chain,
{
    fn height(&self) -> Height;

    fn add(&mut self, state: TrustedState<C::Commit, C::Header>) -> Result<(), error::Error>;

    fn get(&self, height: Height) -> Result<&TrustedState<C::Commit, C::Header>, error::Error>;

    fn has(&self, height: Height) -> bool {
        self.get(height).is_ok()
    }
}
