use crate::base::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::impls::messages::skip_update_client::SkipUpdateClient;
use crate::base::impls::messages::wait_update_client::WaitUpdateClient;
use crate::base::impls::packet_relayers::base_ack_packet::BaseAckPacketRelayer;
use crate::base::impls::packet_relayers::base_receive_packet::BaseReceivePacketRelayer;
use crate::base::impls::packet_relayers::full_relay::FullRelayer;
use crate::base::impls::packet_relayers::retry::RetryRelayer;
use crate::base::impls::packet_relayers::skip_received_packet::SkipReceivedPacketRelayer;
use crate::base::one_for_all::impls::chain::OfaConsensusStateQuerier;
use crate::base::one_for_all::impls::relay::OfaUpdateClientMessageBuilder;
use crate::base::one_for_all::impls::status::OfaChainStatusQuerier;
use crate::base::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use crate::base::one_for_all::traits::components::chain::{
    OfaChainComponents, OfaIbcChainComponents,
};
use crate::base::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::base::one_for_all::traits::relay::OfaRelay;

pub struct BaseComponents;

impl<Chain> OfaChainComponents<Chain> for BaseComponents
where
    Chain: OfaChain,
{
    type ChainStatusQuerier = OfaChainStatusQuerier;
}

impl<Chain, Counterparty> OfaIbcChainComponents<Chain, Counterparty> for BaseComponents
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = OfaConsensusStateQuerier;
}

impl<Relay> OfaRelayComponents<Relay> for BaseComponents
where
    Relay: OfaRelay<Components = BaseComponents>,
{
    type PacketRelayer = RetryRelayer<FullRelayer>;

    type ReceivePacketRelayer = SkipReceivedPacketRelayer<BaseReceivePacketRelayer>;

    type AckPacketRelayer = BaseAckPacketRelayer;

    type UpdateClientMessageBuilder =
        SkipUpdateClient<WaitUpdateClient<OfaUpdateClientMessageBuilder>>;

    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}
