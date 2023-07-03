use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstConnectionId, SrcConnectionId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayConnectionOpenAck: HasRelayChains {
    async fn relay_connection_open_ack(
        &self,
        src_connection_id: &SrcConnectionId<Self>,
        dst_connection_id: &DstConnectionId<Self>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait ConnectionOpenAckRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_connection_open_ack(
        relay: &Relay,
        src_connection_id: &SrcConnectionId<Relay>,
        dst_connection_id: &DstConnectionId<Relay>,
    ) -> Result<(), Relay::Error>;
}
