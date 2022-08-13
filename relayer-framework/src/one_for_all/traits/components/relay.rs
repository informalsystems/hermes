use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::components::chain::OfaChainComponents;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::traits::ibc_message_sender::{HasIbcMessageSender, IbcMessageSender};
use crate::traits::messages::update_client::{CanUpdateClient, UpdateClientMessageBuilder};
use crate::traits::packet_relayer::PacketRelayer;
use crate::traits::target::{DestinationTarget, SourceTarget};

pub trait OfaRelayComponents<Relay>
where
    Relay: OfaRelay,
{
    type PacketRelayer: PacketRelayer<OfaRelayContext<Relay>>;

    type SrcUpdateClientMessageBuilder: UpdateClientMessageBuilder<
        OfaRelayContext<Relay>,
        SourceTarget,
    >;

    type DstUpdateClientMessageBuilder: UpdateClientMessageBuilder<
        OfaRelayContext<Relay>,
        DestinationTarget,
    >;

    type SrcIbcMessageSender: IbcMessageSender<OfaRelayContext<Relay>, SourceTarget>;

    type DstIbcMessageSender: IbcMessageSender<OfaRelayContext<Relay>, DestinationTarget>;
}

pub trait OfaRelayWithComponents: OfaRelay<Components = Self::ComponentsInstance> {
    type ComponentsInstance: OfaRelayComponents<Self>
        + OfaChainComponents<Self::SrcChain>
        + OfaChainComponents<Self::DstChain>;
}

impl<Relay> OfaRelayWithComponents for Relay
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>
        + OfaChainComponents<Self::SrcChain>
        + OfaChainComponents<Self::DstChain>,
{
    type ComponentsInstance = Relay::Components;
}

impl<Relay, Components> CanUpdateClient<SourceTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type UpdateClientMessageBuilder = Components::SrcUpdateClientMessageBuilder;
}

impl<Relay, Components> CanUpdateClient<DestinationTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type UpdateClientMessageBuilder = Components::DstUpdateClientMessageBuilder;
}

impl<Relay, Components> HasIbcMessageSender<SourceTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type IbcMessageSender = Components::SrcIbcMessageSender;
}

impl<Relay, Components> HasIbcMessageSender<DestinationTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    type IbcMessageSender = Components::DstIbcMessageSender;
}
