use std::path::Path;

use serde::{de::DeserializeOwned, Serialize};

use tendermint::lite::types as tmlite;
use tendermint::lite::{Height, TrustedState};

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;

pub mod mem;
pub mod sled;

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

    fn get(&self, height: StoreHeight) -> Result<TrustedState<C::Commit, C::Header>, error::Error>;

    fn has(&self, height: StoreHeight) -> bool {
        self.get(height).is_ok()
    }

    fn get_trust_options(&self) -> Result<TrustOptions, error::Error>;
    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error>;
}

pub fn persistent<C: Chain>(path: impl AsRef<Path>) -> sled::SledStore<C>
where
    <<C as Chain>::Commit as tmlite::Commit>::ValidatorSet: Serialize + DeserializeOwned,
{
    sled::SledStore::new(path)
}

pub fn in_memory<C: Chain>() -> mem::MemStore<C> {
    mem::MemStore::new()
}
