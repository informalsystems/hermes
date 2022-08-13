use alloc::sync::Arc;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics24_host::identifier::ClientId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::traits::contexts::error::HasError;
use ibc_relayer_framework::traits::contexts::relay::RelayContext;
use ibc_relayer_framework::traits::contexts::runtime::HasRuntime;
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::ibc_message_sender::HasIbcMessageSender;
use ibc_relayer_framework::traits::target::{DestinationTarget, SourceTarget};
use tokio::runtime::Runtime;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::runtime::CosmosRuntime;
use crate::cosmos::error::Error;

#[derive(Clone)]
pub struct CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    pub src_handle: CosmosChainContext<SrcChain>,
    pub dst_handle: CosmosChainContext<DstChain>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    pub runtime: Arc<Runtime>,
}

impl<SrcChain, DstChain> CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new(
        src_handle: CosmosChainContext<SrcChain>,
        dst_handle: CosmosChainContext<DstChain>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    ) -> Self {
        let runtime = Arc::new(Runtime::new().unwrap());

        let context = Self {
            src_handle,
            dst_handle,
            src_to_dst_client,
            dst_to_src_client,
            runtime: runtime.clone(),
        };

        context
    }
}

impl<SrcChain, DstChain> HasError for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type Error = Error;
}

impl<SrcChain, DstChain> HasRuntime for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type Runtime = CosmosRuntime;

    fn runtime(&self) -> &CosmosRuntime {
        &CosmosRuntime
    }
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

impl<SrcChain, DstChain> HasIbcMessageSender<SourceTarget>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}

impl<SrcChain, DstChain> HasIbcMessageSender<DestinationTarget>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
