use crate::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::impls::messages::skip_update_client::SkipUpdateClient;
use crate::impls::messages::wait_update_client::WaitUpdateClient;
use crate::impls::packet_relayers::top::TopRelayer;
use crate::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use crate::one_for_all::impls::status::OfaChainStatusQuerier;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::components::chain::OfaChainComponents;
use crate::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::one_for_all::traits::relay::OfaRelay;

pub struct DefaultComponents;

impl<Chain> OfaChainComponents<Chain> for DefaultComponents
where
    Chain: OfaChain,
{
    type ChainStatusQuerier = OfaChainStatusQuerier;
}

impl<Relay> OfaRelayComponents<Relay> for DefaultComponents
where
    Relay: OfaRelay<Components = DefaultComponents>,
{
    type PacketRelayer = TopRelayer;

    type SrcUpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type DstUpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type SrcIbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;

    type DstIbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
