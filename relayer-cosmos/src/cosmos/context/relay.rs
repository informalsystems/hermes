use alloc::sync::Arc;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics24_host::identifier::ClientId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::core::ErrorContext;
use ibc_relayer_framework::traits::ibc_message_sender::IbcMessageSenderContext;
use ibc_relayer_framework::traits::relay_context::RelayContext;
use ibc_relayer_framework::traits::runtime::context::RuntimeContext;
use ibc_relayer_framework::traits::target::{DestinationTarget, SourceTarget};
use tokio::runtime::Runtime;
use tokio::sync::mpsc::{channel, Sender};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::runtime::CosmosRuntimeContext;
use crate::cosmos::error::Error;
use crate::cosmos::message_senders::batch::{
    BatchConfig, BatchMessageContext, BatchedMessageSender, MessageBatch,
};

pub type CosmosMessageSender =
    BatchedMessageSender<SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>>;

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
    pub src_message_sink: Sender<MessageBatch<Self, SourceTarget>>,
    pub dst_message_sink: Sender<MessageBatch<Self, DestinationTarget>>,
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
        batch_config: BatchConfig,
    ) -> Arc<Self> {
        let (src_message_sink, src_message_receiver) = channel(batch_config.buffer_size);
        let (dst_message_sink, dst_message_receiver) = channel(batch_config.buffer_size);

        let runtime = Arc::new(Runtime::new().unwrap());

        let context = Arc::new(Self {
            src_handle,
            dst_handle,
            src_to_dst_client,
            dst_to_src_client,
            runtime: runtime.clone(),
            src_message_sink,
            dst_message_sink,
        });

        CosmosMessageSender::spawn_batch_message_handler::<_, SourceTarget>(
            context.clone(),
            batch_config.clone(),
            &runtime,
            src_message_receiver,
        );

        CosmosMessageSender::spawn_batch_message_handler::<_, DestinationTarget>(
            context.clone(),
            batch_config,
            &runtime,
            dst_message_receiver,
        );

        context
    }
}

impl<SrcChain, DstChain> ErrorContext for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type Error = Error;
}

impl<SrcChain, DstChain> RuntimeContext for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type Runtime = CosmosRuntimeContext;

    fn runtime(&self) -> &CosmosRuntimeContext {
        &CosmosRuntimeContext
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

impl<SrcChain, DstChain> IbcMessageSenderContext<SourceTarget>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
    // BatchedMessageSender<SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>>;
}

impl<SrcChain, DstChain> IbcMessageSenderContext<DestinationTarget>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
    // BatchedMessageSender<SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>>;
}

impl<SrcChain, DstChain> BatchMessageContext<SourceTarget>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    fn message_sink(&self) -> &Sender<MessageBatch<Self, SourceTarget>> {
        &self.src_message_sink
    }
}

impl<SrcChain, DstChain> BatchMessageContext<DestinationTarget>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    fn message_sink(&self) -> &Sender<MessageBatch<Self, DestinationTarget>> {
        &self.dst_message_sink
    }
}
