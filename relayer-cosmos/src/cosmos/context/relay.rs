use async_trait::async_trait;
use core::time::Duration;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics24_host::identifier::ClientId;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::core::ErrorContext;
use ibc_relayer_framework::traits::relay_context::RelayContext;
use ibc_relayer_framework::traits::sleep::SleepContext;
use tokio::time::sleep;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::error::Error;

#[derive(Clone)]
pub struct CosmosRelayContext<SrcChain, DstChain> {
    pub src_handle: CosmosChainContext<SrcChain>,
    pub dst_handle: CosmosChainContext<DstChain>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
}

impl<SrcChain, DstChain> ErrorContext for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type Error = Error;
}

impl<SrcChain, DstChain> RelayContext for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type SrcChain = CosmosChainContext<SrcChain>;

    type DstChain = CosmosChainContext<DstChain>;

    type Packet = Packet;

    fn source_chain(&self) -> &Self::SrcChain {
        &self.src_handle
    }

    fn destination_chain(&self) -> &Self::DstChain {
        &self.dst_handle
    }

    fn source_client_id(&self) -> &ClientId {
        &self.dst_to_src_client.id
    }

    fn destination_client_id(&self) -> &ClientId {
        &self.src_to_dst_client.id
    }
}

#[async_trait]
impl<SrcChain, DstChain> SleepContext for CosmosRelayContext<SrcChain, DstChain> {
    async fn sleep(duration: Duration) {
        sleep(duration).await;
    }
}
