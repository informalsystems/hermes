use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::types::connection::HasConnectionVersionType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{SrcConnectionId, SrcConnectionVersion};
use crate::std_prelude::*;

#[async_trait]
pub trait CanInitConnection: HasRelayChains
where
    Self::SrcChain: HasConnectionVersionType<Self::DstChain>,
{
    async fn init_connection(
        &self,
        version: SrcConnectionVersion<Self>,
        connection_delay: Duration,
    ) -> Result<SrcConnectionId<Self>, Self::Error>;
}

#[async_trait]
pub trait ConnectionInitializer<Relay>
where
    Relay: HasRelayChains,
    Relay::SrcChain: HasConnectionVersionType<Relay::DstChain>,
{
    async fn init_connection(
        relay: &Relay,
        version: &SrcConnectionVersion<Relay>,
        delay_period: Duration,
    ) -> Result<SrcConnectionId<Relay>, Relay::Error>;
}
