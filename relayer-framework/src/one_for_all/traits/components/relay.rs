use crate::one_for_all::traits::components::chain::OfaChainComponents;
use crate::one_for_all::traits::relay::OfaRelay;

pub trait OfaRelayComponents<Relay>:
    OfaChainComponents<Relay::SrcChain> + OfaChainComponents<Relay::DstChain>
where
    Relay: OfaRelay,
{
}

pub trait OfaRelayWithComponents: OfaRelay<Components = Self::ComponentsInstance> {
    type ComponentsInstance: OfaRelayComponents<Self>;
}

impl<Relay> OfaRelayWithComponents for Relay
where
    Relay: OfaRelay,
    Relay::Components: OfaRelayComponents<Relay>,
{
    type ComponentsInstance = Relay::Components;
}
