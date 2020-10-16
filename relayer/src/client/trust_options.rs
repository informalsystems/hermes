use std::time::Duration;

use anomaly::fail;
use serde_derive::{Deserialize, Serialize};

use tendermint::block::Height;
use tendermint::Hash;
use tendermint_light_client::types::TrustThreshold;

use crate::error;

/// The trust options for a `Client`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustOptions {
    pub header_hash: Hash,
    pub height: Height,
    pub trusting_period: Duration,
    pub trust_threshold: TrustThreshold,
}

impl TrustOptions {
    pub fn new(
        header_hash: Hash,
        height: Height,
        trusting_period: Duration,
        trust_threshold: TrustThreshold,
    ) -> Result<Self, error::Error> {
        if trusting_period <= Duration::new(0, 0) {
            fail!(
                error::Kind::LightClient,
                "trusting period must be greater than zero"
            )
        }

        Ok(Self {
            header_hash,
            height,
            trusting_period,
            trust_threshold,
        })
    }
}
