use std::time::Duration;

use anomaly::fail;

use tendermint::lite::{Height, TrustThreshold};
use tendermint::Hash;

use crate::error;

pub struct TrustOptions<TT>
where
    TT: TrustThreshold,
{
    pub period: Duration,
    pub height: Height,
    pub hash: Hash,
    pub trust_threshold: TT,
}

impl<TT> TrustOptions<TT>
where
    TT: TrustThreshold,
{
    pub fn new(
        period: Duration,
        height: Height,
        hash: Hash,
        trust_threshold: TT,
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
