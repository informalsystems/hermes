use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::traits::ibc_message_sender::{HasIbcMessageSender, IbcMessageSender};
use ibc_relayer_framework::traits::message_sender::MessageSender;
use ibc_relayer_framework::traits::target::{DestinationTarget, SourceTarget};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;
use crate::cosmos::message_sender::CosmosBaseMessageSender;

pub fn base_message_sender<Chain>() -> impl MessageSender<CosmosChainContext<Chain>>
where
    Chain: ChainHandle,
{
    CosmosBaseMessageSender
}

pub fn base_source_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayContext<SrcChain, DstChain>, SourceTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesToChain
}

pub fn base_destination_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayContext<SrcChain, DstChain>, DestinationTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesToChain
}

pub fn source_update_client_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayContext<SrcChain, DstChain>, SourceTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesWithUpdateClient(SendIbcMessagesToChain)
}

pub fn destination_update_client_message_sender<SrcChain, DstChain>(
) -> impl IbcMessageSender<CosmosRelayContext<SrcChain, DstChain>, DestinationTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    SendIbcMessagesWithUpdateClient(SendIbcMessagesToChain)
}

pub fn source_message_sender_context<SrcChain, DstChain>(
    handler: &CosmosRelayContext<SrcChain, DstChain>,
) -> &impl HasIbcMessageSender<SourceTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    handler
}

pub fn destination_message_sender_context<SrcChain, DstChain>(
    handler: &CosmosRelayContext<SrcChain, DstChain>,
) -> &impl HasIbcMessageSender<DestinationTarget>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    handler
}
