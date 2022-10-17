use crate::base::one_for_all::traits::chain::OfaIbcChainComponents;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::{
    HasTimeoutUnorderedPacketRelayer, TimeoutUnorderedPacketRelayer,
};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};

pub trait OfaRelayComponents<Relay>:
    OfaIbcChainComponents<Relay::SrcChain, Relay::DstChain>
    + OfaIbcChainComponents<Relay::DstChain, Relay::SrcChain>
where
    Relay: OfaBaseRelay,
{
    type PacketRelayer: PacketRelayer<OfaRelayWrapper<Relay>>;

    type ReceivePacketRelayer: ReceivePacketRelayer<OfaRelayWrapper<Relay>>;

    type AckPacketRelayer: AckPacketRelayer<OfaRelayWrapper<Relay>>;

    type TimeoutUnorderedPacketRelayer: TimeoutUnorderedPacketRelayer<OfaRelayWrapper<Relay>>;

    type UpdateClientMessageBuilder: UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, SourceTarget>
        + UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, DestinationTarget>;

    type IbcMessageSender: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}

impl<Relay, Components> HasTimeoutUnorderedPacketRelayer for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type TimeoutUnorderedPacketRelayer = Components::TimeoutUnorderedPacketRelayer;
}
