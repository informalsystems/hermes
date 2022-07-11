use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::traits::ibc_message_sender::{
    IbcMessageSender, IbcMessageSenderContext,
};
use ibc_relayer_framework::traits::message_sender::MessageSender;
use ibc_relayer_framework::traits::target::{DestinationTarget, SourceTarget};

use crate::cosmos::handler::{CosmosChainHandler, CosmosRelayHandler};
use crate::cosmos::message_sender::CosmosBaseMessageSender;

pub fn base_message_sender<Chain>() -> impl MessageSender<CosmosChainHandler<Chain>>
where
    Chain: ChainHandle,
{
    CosmosBaseMessageSender
}

pub fn base_source_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayHandler<SrcChain, DstChain>, SourceTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesToChain
}

pub fn base_destination_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayHandler<SrcChain, DstChain>, DestinationTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesToChain
}

pub fn source_update_client_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayHandler<SrcChain, DstChain>, SourceTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesWithUpdateClient(SendIbcMessagesToChain)
}

pub fn destination_update_client_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayHandler<SrcChain, DstChain>, DestinationTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesWithUpdateClient(SendIbcMessagesToChain)
}

pub fn source_message_sender_context<SrcChain, DstChain>(
    handler: &CosmosRelayHandler<SrcChain, DstChain>,
) -> &impl IbcMessageSenderContext<SourceTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    handler
}

pub fn destination_message_sender_context<SrcChain, DstChain>(
    handler: &CosmosRelayHandler<SrcChain, DstChain>,
) -> &impl IbcMessageSenderContext<DestinationTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    handler
}
