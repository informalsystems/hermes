pub mod ccv_double_voting;
pub mod ccv_misbehaviour;
pub mod error;

use std::convert::Infallible;

use derive_more::Display;
use ibc_proto::interchain_security::ccv::provider::v1::Chain;
use serde::{Deserialize, Serialize};

use crate::core::ics24_host;
use crate::core::ics24_host::identifier::{ChainId, ClientId};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display, Serialize, Deserialize)]
pub struct ConsumerId(String);

impl ConsumerId {
    pub const fn new(id: String) -> Self {
        Self(id)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::str::FromStr for ConsumerId {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(s.to_string()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsumerChain {
    pub chain_id: ChainId,
    pub consumer_id: ConsumerId,
    pub client_id: ClientId,
}

impl TryFrom<Chain> for ConsumerChain {
    type Error = ics24_host::error::ValidationError;

    fn try_from(value: Chain) -> Result<Self, Self::Error> {
        Ok(Self {
            chain_id: ChainId::from_string(&value.chain_id),
            consumer_id: ConsumerId::new(value.consumer_id),
            client_id: value.client_id.parse()?,
        })
    }
}
