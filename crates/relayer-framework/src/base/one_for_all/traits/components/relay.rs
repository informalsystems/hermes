use crate::base::one_for_all::traits::components::chain::OfaIbcChainComponents;
use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayWrapper};
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
    type PacketRelayer: PacketRelayer<OfaRelayWrapper<Relay>>;

    type UpdateClientMessageBuilder: UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, SourceTarget>
        + UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, DestinationTarget>;

    type IbcMessageSender: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}

impl<Relay, Components> HasUpdateClientMessageBuilder<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type UpdateClientMessageBuilder = Components::UpdateClientMessageBuilder;
}

impl<Relay, Components> HasUpdateClientMessageBuilder<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type UpdateClientMessageBuilder = Components::UpdateClientMessageBuilder;
}

impl<Relay, Components> HasIbcMessageSender<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type IbcMessageSender = Components::IbcMessageSender;
}

impl<Relay, Components> HasIbcMessageSender<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type IbcMessageSender = Components::IbcMessageSender;
}
