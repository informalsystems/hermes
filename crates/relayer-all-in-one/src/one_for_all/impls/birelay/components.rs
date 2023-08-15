use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::components::extra::ExtraComponents;

use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::component::OfaComponents;

impl<BiRelay, Name> DelegateComponent<Name> for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: Async,
{
    type Delegate = ExtraComponents<OfaComponents>;
}
