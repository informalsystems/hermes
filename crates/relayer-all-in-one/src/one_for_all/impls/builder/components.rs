use ibc_relayer_components::core::traits::component::{DelegateComponent, HasComponents};
use ibc_relayer_components_extra::components::extra::build::ExtraBuildComponents;

use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::component::OfaComponents;

impl<Build> HasComponents for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type Components = ExtraBuildComponents<OfaComponents>;
}

impl<Build, Name> DelegateComponent<Name> for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type Delegate = ExtraBuildComponents<OfaComponents>;
}
