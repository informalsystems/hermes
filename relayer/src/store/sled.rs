use std::{marker::PhantomData, path::Path};

use anomaly::fail;

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;
use crate::util::sled::{self as sled_util, KeyValueDb, SingleDb};

use super::{Store, StoreHeight};

/// Persistent store backed by an on-disk `sled` database.
///
/// TODO: Remove this hideous `where` clause, once we enforce in
/// tendermint-rs that validator sets must be serializable.
#[derive(Debug)]
pub struct SledStore<C: Chain> {
    db: sled::Db,
    trust_options_db: SingleDb<TrustOptions>,
    marker: PhantomData<C>,
}

impl<C: Chain> SledStore<C> {
    pub fn new(path: impl AsRef<Path>) -> Result<Self, error::Error> {
        let db = sled::open(path).map_err(|e| error::Kind::Store.context(e))?;

        Ok(Self {
            db,
            trust_options_db: sled_util::single("trust_options/"),
            marker: PhantomData,
        })
    }
}

impl<C: Chain> Store<C> for SledStore<C> {
    fn get_trust_options(&self) -> Result<TrustOptions, error::Error> {
        let trust_options = self.trust_options_db.get(&self.db)?;

        match trust_options {
            Some(trust_options) => Ok(trust_options),
            None => fail!(error::Kind::Store, "no trust options in trusted store"),
        }
    }

    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error> {
        self.trust_options_db.set(&self.db, &trust_options)
    }
}
