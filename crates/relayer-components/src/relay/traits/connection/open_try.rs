use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::connection::HasConnectionOpenTryEvent;
use crate::relay::traits::chains::HasRelayChains;
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayConnectionOpenTry: HasRelayChains
where
    Self::DstChain: HasConnectionOpenTryEvent<Self::SrcChain>,
{
    async fn relay_connection_open_try(
        &self,
        connection_id: &<Self::SrcChain as HasIbcChainTypes<Self::DstChain>>::ConnectionId,
    ) -> Result<
        <Self::DstChain as HasConnectionOpenTryEvent<Self::SrcChain>>::ConnectionOpenTryEvent,
        Self::Error,
    >;
}

#[async_trait]
pub trait ConnectionOpenTryRelayer<Relay>
where
    Relay: HasRelayChains,
    Relay::DstChain: HasConnectionOpenTryEvent<Relay::SrcChain>,
{
    async fn relay_connection_open_try(
        relay: &Relay,
        connection_id: &<Relay::SrcChain as HasIbcChainTypes<Relay::DstChain>>::ConnectionId,
    ) -> Result<
        <Relay::DstChain as HasConnectionOpenTryEvent<Relay::SrcChain>>::ConnectionOpenTryEvent,
        Relay::Error,
    >;
}
