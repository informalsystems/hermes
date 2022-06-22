use async_trait::async_trait;

use super::context::RelayContext;
use crate::types::packet::Packet;

#[async_trait]
pub trait StateMachine: RelayContext {
    type NextState;

    async fn relay(
        &self,
        packet: Packet<Self::SrcChain, Self::DstChain>,
    ) -> Result<Self::NextState, Self::Error>;
}
