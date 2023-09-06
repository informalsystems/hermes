use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components_extra::components::extra::build::ExtraBuildComponents;
use ibc_relayer_components_extra::components::extra::closures::build::CanUseExtraBuilderComponents;

use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::component::OfaComponents;

impl<Build> HasComponents for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type Components = ExtraBuildComponents<OfaComponents>;
}

impl<Build> CanUseExtraBuilderComponents for OfaBuilderWrapper<Build> where Build: OfaBuilder {}
