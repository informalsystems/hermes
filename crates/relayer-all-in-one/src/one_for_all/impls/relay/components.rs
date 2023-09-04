use ibc_relayer_components::core::traits::component::{DelegateComponent, HasComponents};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::components::extra::relay::ExtraRelayComponents;

use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> HasComponents for OfaRelayWrapper<Relay>
where
    Relay: Async,
{
    type Components = ExtraRelayComponents<OfaComponents>;
}

impl<Relay, Name> DelegateComponent<Name> for OfaRelayWrapper<Relay>
where
    Relay: Async,
{
    type Delegate = ExtraRelayComponents<OfaComponents>;
}
