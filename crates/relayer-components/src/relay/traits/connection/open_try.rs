use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstConnectionId, SrcConnectionId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayConnectionOpenTry: HasRelayChains {
    async fn relay_connection_open_try(
        &self,
        src_connection_id: &SrcConnectionId<Self>,
    ) -> Result<DstConnectionId<Self>, Self::Error>;
}

#[async_trait]
pub trait ConnectionOpenTryRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_connection_open_try(
        relay: &Relay,
        src_connection_id: &SrcConnectionId<Relay>,
    ) -> Result<DstConnectionId<Relay>, Relay::Error>;
}
