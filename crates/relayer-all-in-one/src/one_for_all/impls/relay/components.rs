use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::components::extra::closures::relay::components::CanUseExtraRelayComponents;
use ibc_relayer_components_extra::components::extra::relay::ExtraRelayComponents;

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> HasComponents for OfaRelayWrapper<Relay>
where
    Relay: Async,
{
    type Components = ExtraRelayComponents<OfaComponents>;
}

impl<Relay> CanUseExtraRelayComponents for OfaRelayWrapper<Relay> where Relay: OfaRelay {}
