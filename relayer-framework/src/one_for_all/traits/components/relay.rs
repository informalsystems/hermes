use crate::core::traits::ibc_message_sender::{HasIbcMessageSender, IbcMessageSender};
use crate::core::traits::messages::update_client::{
    HasUpdateClientMessageBuilder, UpdateClientMessageBuilder,
};
use crate::core::traits::packet_relayer::PacketRelayer;
use crate::core::traits::target::{DestinationTarget, SourceTarget};
use crate::one_for_all::traits::relay::{OfaRelay, OfaRelayContext};

pub trait OfaRelayComponents<Relay>
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
