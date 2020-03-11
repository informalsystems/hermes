use std::time::Duration;

use anomaly::fail;

use tendermint::lite::{Height, TrustThresholdFraction};
use tendermint::Hash;

use crate::error;

pub struct TrustOptions {
    pub period: Duration,
    pub height: Height,
    pub hash: Hash,
    pub trust_threshold: TrustThresholdFraction,
}

impl TrustOptions {
    pub fn new(
        period: Duration,
        height: Height,
        hash: Hash,
        trust_threshold: TrustThresholdFraction,
    ) -> Result<Self, error::Error> {
        if period <= Duration::new(0, 0) {
            fail!(
                error::Kind::LightClient,
                "trust options period must be greater than zero"
            )
        }

        Ok(Self {
            period,
            height,
            hash,
            trust_threshold,
        })
    }
}
