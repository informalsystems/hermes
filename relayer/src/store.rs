use std::path::Path;

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;

use tendermint::block::Height;

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
    /// Get the trust options configured for the associated chain, if any
    fn get_trust_options(&self) -> Result<TrustOptions, error::Error>;

    /// Set the trust options for the associated chain
    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error>;
}

/// Returns a persistent trusted store backed by an on-disk `sled` database
/// stored in the folder specified in the `path` argument.
pub fn persistent<C: Chain>(db_path: impl AsRef<Path>) -> Result<sled::SledStore<C>, error::Error> {
    sled::SledStore::new(db_path)
}

/// Returns a transient in-memory store
pub fn in_memory<C: Chain>() -> mem::MemStore<C> {
    mem::MemStore::new()
}
