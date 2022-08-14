use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_framework::impls::messages::wait_update_client::WaitUpdateClient;
use ibc_relayer_framework::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use ibc_relayer_framework::one_for_all::impls::status::OfaChainStatusQuerier;
use ibc_relayer_framework::one_for_all::traits::components::chain::OfaChainComponents;
use ibc_relayer_framework::one_for_all::traits::components::relay::OfaRelayComponents;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;

pub struct CosmosComponents;

impl<Handle> OfaChainComponents<CosmosChainContext<Handle>> for CosmosComponents
where
    Handle: ChainHandle,
{
    type ChainStatusQuerier = OfaChainStatusQuerier;
}

impl<SrcHandle, DstHandle> OfaRelayComponents<CosmosRelayContext<SrcHandle, DstHandle>>
    for CosmosComponents
where
    SrcHandle: ChainHandle,
    DstHandle: ChainHandle,
{
    type PacketRelayer = TopRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
