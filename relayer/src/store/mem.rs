use std::marker::PhantomData;

use anomaly::fail;

use super::Store;

use crate::chain::Chain;
use crate::client::trust_options::TrustOptions;
use crate::error;

/// Transient in-memory store
pub struct MemStore<C: Chain> {
    trust_options: Option<TrustOptions>,
    marker: PhantomData<C>,
}

impl<C: Chain> MemStore<C> {
    pub fn new() -> Self {
        Self {
            trust_options: None,
            marker: PhantomData,
        }
    }
}

impl<C: Chain> Default for MemStore<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: Chain> Store<C> for MemStore<C> {
    fn get_trust_options(&self) -> Result<TrustOptions, error::Error> {
        match self.trust_options {
            Some(ref trust_options) => Ok(trust_options.clone()),
            None => fail!(error::Kind::Store, "no trust options in trusted store"),
        }
    }

    fn set_trust_options(&mut self, trust_options: TrustOptions) -> Result<(), error::Error> {
        self.trust_options = Some(trust_options);
        Ok(())
    }
}
