use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstConnectionId, SrcConnectionId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayConnectionOpenHandshake: HasRelayChains {
    async fn relay_connection_open_handshake(
        &self,
        src_connection_id: &SrcConnectionId<Self>,
    ) -> Result<DstConnectionId<Self>, Self::Error>;
}

#[async_trait]
pub trait ConnectionOpenHandshakeRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_connection_open_handshake(
        relay: &Relay,
        connection_id: &SrcConnectionId<Relay>,
    ) -> Result<DstConnectionId<Relay>, Relay::Error>;
}
