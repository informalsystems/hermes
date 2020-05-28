use std::path::Path;

use tendermint::lite::{Height, TrustedState};

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;

/// In-memory store
pub mod mem;

/// Persistent store via the `sled` database
pub mod sled;

/// Either the last stored height or a given one
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StoreHeight {
    /// The last stored height
    Last,

    /// The given height
    Given(Height),
}

/// Defines a trusted store, which tracks:
///
/// - the latest height a light client as synced up to
/// - all the trusted state (header+commit) the light client has verified
/// - the trust options configured for the associated chain
pub trait Store<C>
where
    C: Chain,
{
    /// Get the last height to which the light client has synced up to, if any
    fn last_height(&self) -> Result<Option<Height>, error::Error>;

    /// Add a trusted state to the store
    fn add(&mut self, state: TrustedState<C::Commit, C::Header>) -> Result<(), error::Error>;

    /// Fetch the trusted state at the given height from the store, if it exists
    fn get(&self, height: StoreHeight) -> Result<TrustedState<C::Commit, C::Header>, error::Error>;

    /// Check whether the trusted store contains a trusted state at the given height
    fn has(&self, height: StoreHeight) -> bool {
        self.get(height).is_ok()
    }

    /// Get the trust options configured for the associated chain, if any
    fn get_trust_options(&self) -> Result<TrustOptions, error::Error>;

    /// Set the trust options for the associated chain
    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error>;
}

/// Returns a persistent trusted store backed by an on-disk `sled` database
/// stored in sthe folder specified in the `path` argument.
pub fn persistent<C: Chain>(db_path: impl AsRef<Path>) -> Result<sled::SledStore<C>, error::Error> {
    sled::SledStore::new(db_path)
}

/// Returns a transient in-memory store
pub fn in_memory<C: Chain>() -> mem::MemStore<C> {
    mem::MemStore::new()
}
