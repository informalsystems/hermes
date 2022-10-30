use async_trait::async_trait;
use ibc_relayer_framework::base::chain::traits::queries::status::{
    CanQueryChainStatus, HasChainStatus,
};
use ibc_relayer_framework::base::chain::traits::types::{
    HasChainTypes, HasEventType, HasMessageType,
};
use ibc_relayer_framework::base::core::traits::error::HasError;

use crate::std_prelude::*;

pub type Natural = u8;

#[derive(Debug)]
pub enum MockError {}

#[derive(Clone)]
pub struct ChainStatus {
    pub height: Natural,
    pub timestamp: Natural,
}

pub struct MockChain {
    pub current_status: ChainStatus,
}

impl HasError for MockChain {
    type Error = MockError;
}

impl HasMessageType for MockChain {
    type Message = String;
}

impl HasEventType for MockChain {
    type Event = String;
}

impl HasChainTypes for MockChain {
    type Height = Natural;
    type Timestamp = Natural;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        Ok(message.len())
    }
}

impl HasChainStatus for MockChain {
    type ChainStatus = ChainStatus;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height {
        &status.height
    }

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp {
        &status.timestamp
    }
}

#[async_trait]
impl CanQueryChainStatus for MockChain {
    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        Ok(self.current_status.clone())
    }
}
