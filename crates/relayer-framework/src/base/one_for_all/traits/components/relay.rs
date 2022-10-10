use crate::base::one_for_all::traits::components::chain::OfaIbcChainComponents;
use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayContext};
use crate::base::traits::ibc_message_sender::{HasIbcMessageSender, IbcMessageSender};
use crate::base::traits::messages::update_client::{
    HasUpdateClientMessageBuilder, UpdateClientMessageBuilder,
};
use crate::base::traits::packet_relayer::PacketRelayer;
use crate::base::traits::target::{DestinationTarget, SourceTarget};

pub trait OfaRelayComponents<Relay>:
    OfaIbcChainComponents<Relay::SrcChain, Relay::DstChain>
    + OfaIbcChainComponents<Relay::DstChain, Relay::SrcChain>
where
    Relay: OfaRelay,
{
    type PacketRelayer: PacketRelayer<OfaRelayContext<Relay>>;

    type UpdateClientMessageBuilder: UpdateClientMessageBuilder<OfaRelayContext<Relay>, SourceTarget>
        + UpdateClientMessageBuilder<OfaRelayContext<Relay>, DestinationTarget>;

    type IbcMessageSender: IbcMessageSender<OfaRelayContext<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayContext<Relay>, DestinationTarget>;
}

impl<Relay, Components> HasUpdateClientMessageBuilder<SourceTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type UpdateClientMessageBuilder = Components::UpdateClientMessageBuilder;
}

impl<Relay, Components> HasUpdateClientMessageBuilder<DestinationTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type UpdateClientMessageBuilder = Components::UpdateClientMessageBuilder;
}

impl<Relay, Components> HasIbcMessageSender<SourceTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type IbcMessageSender = Components::IbcMessageSender;
}

impl<Relay, Components> HasIbcMessageSender<DestinationTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type IbcMessageSender = Components::IbcMessageSender;
}
