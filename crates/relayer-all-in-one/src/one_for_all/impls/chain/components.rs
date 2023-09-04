use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::components::extra::chain::ExtraChainComponents;

use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::component::OfaComponents;

impl<Chain> HasComponents for OfaChainWrapper<Chain>
where
    Chain: Async,
{
    type Components = ExtraChainComponents<OfaComponents>;
}
