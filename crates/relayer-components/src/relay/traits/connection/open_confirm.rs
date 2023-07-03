use async_trait::async_trait;

use crate::relay::traits::chains::HasRelayChains;
use crate::relay::types::aliases::{DstConnectionId, SrcConnectionId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayConnectionOpenConfirm: HasRelayChains {
    async fn relay_connection_open_confirm(
        &self,
        src_connection_id: &SrcConnectionId<Self>,
        dst_connection_id: &DstConnectionId<Self>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait ConnectionOpenConfirmRelayer<Relay>
where
    Relay: HasRelayChains,
{
    async fn relay_connection_open_confirm(
        relay: &Relay,
        src_connection_id: &SrcConnectionId<Relay>,
        dst_connection_id: &DstConnectionId<Relay>,
    ) -> Result<(), Relay::Error>;
}
