use std::time::Duration;

use anomaly::fail;

use tendermint::lite::{Height, TrustThresholdFraction};
use tendermint::Hash;

use crate::error;

pub struct TrustOptions {
    pub hash: Hash,
    pub height: Height,
    pub trusting_period: Duration,
    pub trust_threshold: TrustThresholdFraction,
}

impl TrustOptions {
    pub fn new(
        hash: Hash,
        height: Height,
        trusting_period: Duration,
        trust_threshold: TrustThresholdFraction,
    ) -> Result<Self, error::Error> {
        if trusting_period <= Duration::new(0, 0) {
            fail!(
                error::Kind::LightClient,
                "trusting period must be greater than zero"
            )
        }

        Ok(Self {
            hash,
            height,
            trusting_period,
            trust_threshold,
        })
    }
}
