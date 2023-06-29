use async_trait::async_trait;

use crate::chain::traits::types::connection::HasInitConnectionOptionsType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_handshake::CanRelayConnectionOpenHandshake;
use crate::relay::traits::connection::open_init::CanInitConnection;
use crate::relay::types::aliases::{DstConnectionId, SrcConnectionId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanBootstrapConnection: HasRelayChains
where
    Self::SrcChain: HasInitConnectionOptionsType<Self::DstChain>,
{
    async fn bootstrap_connection(
        &self,
        init_connection_options: &<Self::SrcChain as HasInitConnectionOptionsType<
            Self::DstChain,
        >>::InitConnectionOptions,
    ) -> Result<(SrcConnectionId<Self>, DstConnectionId<Self>), Self::Error>;
}

#[async_trait]
impl<Relay, SrcChain, DstChain> CanBootstrapConnection for Relay
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanInitConnection
        + CanRelayConnectionOpenHandshake,
    SrcChain: HasInitConnectionOptionsType<DstChain>,
    DstChain: HasIbcChainTypes<SrcChain>,
{
    async fn bootstrap_connection(
        &self,
        init_connection_options: &SrcChain::InitConnectionOptions,
    ) -> Result<(SrcChain::ConnectionId, DstChain::ConnectionId), Self::Error> {
        let src_connection_id = self.init_connection(init_connection_options).await?;

        let dst_connection_id = self
            .relay_connection_open_handshake(&src_connection_id)
            .await?;

        Ok((src_connection_id, dst_connection_id))
    }
}
