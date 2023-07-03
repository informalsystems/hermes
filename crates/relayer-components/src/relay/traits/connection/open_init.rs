use async_trait::async_trait;

use crate::chain::traits::types::connection::HasInitConnectionOptionsType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::SrcConnectionId;
use crate::std_prelude::*;

#[async_trait]
pub trait CanInitConnection: HasRelayChains
where
    Self::SrcChain: HasInitConnectionOptionsType<Self::DstChain>,
{
    async fn init_connection(
        &self,
        init_connection_options: &<Self::SrcChain as HasInitConnectionOptionsType<
            Self::DstChain,
        >>::InitConnectionOptions,
    ) -> Result<SrcConnectionId<Self>, Self::Error>;
}

#[async_trait]
pub trait ConnectionInitializer<Relay>
where
    Relay: HasRelayChains,
    Relay::SrcChain: HasInitConnectionOptionsType<Relay::DstChain>,
{
    async fn init_connection(
        relay: &Relay,
        init_connection_options: &<Relay::SrcChain as HasInitConnectionOptionsType<
            Relay::DstChain,
        >>::InitConnectionOptions,
    ) -> Result<SrcConnectionId<Relay>, Relay::Error>;
}
