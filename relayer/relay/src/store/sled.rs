use std::path::Path;

use anomaly::fail;

use tendermint::lite::types::Header as _;
use tendermint::lite::{Height, TrustedState};

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
    last_height_db: SingleDb<Height>,
    trust_options_db: SingleDb<TrustOptions>,
    trusted_state_db: KeyValueDb<Height, TrustedState<C::Commit, C::Header>>,
}

impl<C: Chain> SledStore<C> {
    pub fn new(path: impl AsRef<Path>) -> Result<Self, error::Error> {
        let db = sled::open(path).map_err(|e| error::Kind::Store.context(e))?;

        Ok(Self {
            db,
            last_height_db: sled_util::single("last_height/"),
            trust_options_db: sled_util::single("trust_options/"),
            trusted_state_db: sled_util::key_value("trusted_state/"),
        })
    }
}

impl<C: Chain> SledStore<C> {
    fn set_last_height(&self, height: Height) -> Result<(), error::Error> {
        self.last_height_db.set(&self.db, &height)
    }
}

impl<C: Chain> Store<C> for SledStore<C> {
    fn last_height(&self) -> Result<Option<Height>, error::Error> {
        self.last_height_db.get(&self.db)
    }

    fn add(
        &mut self,
        trusted_state: TrustedState<C::Commit, C::Header>,
    ) -> Result<(), error::Error> {
        let height = trusted_state.last_header().header().height();

        self.trusted_state_db
            .insert(&self.db, &height, &trusted_state)?;

        self.set_last_height(height)?;

        Ok(())
    }

    fn get(&self, height: StoreHeight) -> Result<TrustedState<C::Commit, C::Header>, error::Error> {
        let height = match height {
            StoreHeight::Last => self.last_height()?.unwrap_or(0),
            StoreHeight::Given(height) => height,
        };

        let state = self.trusted_state_db.fetch(&self.db, &height)?;

        match state {
            Some(state) => Ok(state),
            None => fail!(
                error::Kind::Store,
                "could not load height {} from store",
                height
            ),
        }
    }

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
