use std::marker::PhantomData;
use std::path::Path;

use anomaly::fail;
use serde::{de::DeserializeOwned, Serialize};

use tendermint::lite::types::{self as tmlite, Header as _};
use tendermint::lite::TrustedState;

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;

use super::{Store, StoreHeight};

pub struct SledStore<C: Chain>
where
    <<C as Chain>::Commit as tmlite::Commit>::ValidatorSet: Serialize + DeserializeOwned,
{
    db: sled::Db,
    marker: PhantomData<C>,
}

impl<C: Chain> SledStore<C>
where
    <<C as Chain>::Commit as tmlite::Commit>::ValidatorSet: Serialize + DeserializeOwned,
{
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            db: sled::open(path).unwrap(), // FIXME: Unwrap
            marker: PhantomData,
        }
    }
}

impl<C: Chain> Store<C> for SledStore<C>
where
    <<C as Chain>::Commit as tmlite::Commit>::ValidatorSet: Serialize + DeserializeOwned,
{
    fn last_height(&self) -> Option<u64> {
        let bytes = self
            .db
            .get(b"last_height")
            .map_err(|e| error::Kind::Store.context(e))
            .unwrap(); // FIXME

        match bytes {
            Some(bytes) => {
                let last_height = serde_cbor::from_slice(&bytes)
                    .map_err(|e| error::Kind::Store.context(e))
                    .unwrap(); // FIXME

                Some(last_height)
            }
            None => None,
        }
    }

    fn add(
        &mut self,
        trusted_state: TrustedState<C::Commit, C::Header>,
    ) -> Result<(), error::Error> {
        let bytes =
            serde_cbor::to_vec(&trusted_state).map_err(|e| error::Kind::Store.context(e))?;

        let key = format!(
            "trusted_state/{}",
            trusted_state.last_header().header().height()
        );

        self.db
            .insert(key.as_bytes(), bytes)
            .map(|_| ())
            .map_err(|e| error::Kind::Store.context(e))?;

        Ok(())
    }

    fn get(&self, height: StoreHeight) -> Result<TrustedState<C::Commit, C::Header>, error::Error> {
        let height = match height {
            StoreHeight::Last => self.last_height().unwrap_or(0),
            StoreHeight::Given(height) => height,
        };

        let key = format!("trusted_state/{}", height);
        let bytes = self
            .db
            .get(&key)
            .map_err(|e| error::Kind::Store.context(e))?;

        match bytes {
            Some(bytes) => {
                let trusted_state =
                    serde_cbor::from_slice(&bytes).map_err(|e| error::Kind::Store.context(e))?;

                Ok(trusted_state)
            }
            None => fail!(
                error::Kind::Store,
                "could not load height {} from store",
                height
            ),
        }
    }

    fn get_trust_options(&self) -> Result<TrustOptions, error::Error> {
        let bytes = self
            .db
            .get(b"trust_options") // TODO: Extract as constant
            .map_err(|e| error::Kind::Store.context(e))?;

        match bytes {
            Some(bytes) => {
                let trust_options =
                    serde_cbor::from_slice(&bytes).map_err(|e| error::Kind::Store.context(e))?;

                Ok(trust_options)
            }
            None => fail!(error::Kind::Store, "no trust options in trusted store"),
        }
    }

    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error> {
        let bytes =
            serde_cbor::to_vec(&trust_options).map_err(|e| error::Kind::Store.context(e))?;

        self.db
            .insert(b"trust_options", bytes)
            .map(|_| ())
            .map_err(|e| error::Kind::Store.context(e))?;

        Ok(())
    }
}
