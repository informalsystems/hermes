use async_trait::async_trait;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::components::extra::ExtraComponents;

use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::component::OfaComponents;

#[async_trait]
impl<BiRelay> HasComponents for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: Async,
{
    type Components = ExtraComponents<OfaComponents>;
}
