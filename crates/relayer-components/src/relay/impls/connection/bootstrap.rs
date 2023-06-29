use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::queries::connection::CanQueryCompatibleConnectionVersions;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_handshake::CanRelayConnectionOpenHandshake;
use crate::relay::traits::connection::open_init::CanInitConnection;
use crate::relay::types::aliases::{DstConnectionId, SrcConnectionId};
use crate::std_prelude::*;

#[async_trait]
pub trait CanBootstrapConnection: HasRelayChains {
    async fn bootstrap_connection(
        &self,
        connection_delay: Duration,
    ) -> Result<(SrcConnectionId<Self>, DstConnectionId<Self>), Self::Error>;
}

#[async_trait]
impl<Relay, SrcChain, DstChain> CanBootstrapConnection for Relay
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanInitConnection
        + CanRelayConnectionOpenHandshake,
    SrcChain: CanQueryCompatibleConnectionVersions<DstChain>,
    DstChain: HasIbcChainTypes<SrcChain>,
{
    async fn bootstrap_connection(
        &self,
        connection_delay: Duration,
    ) -> Result<(SrcChain::ConnectionId, DstChain::ConnectionId), Self::Error> {
        let compatible_versions = self
            .src_chain()
            .query_compatible_connection_versions()
            .await
            .map_err(Relay::src_chain_error)?;

        let connection_version = compatible_versions
            .into_iter()
            .next()
            .unwrap_or_else(Default::default);

        let src_connection_id = self
            .init_connection(connection_version, connection_delay)
            .await?;

        let dst_connection_id = self
            .relay_connection_open_handshake(&src_connection_id)
            .await?;

        Ok((src_connection_id, dst_connection_id))
    }
}
