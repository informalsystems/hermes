use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;
use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components_extra::components::extra::build::ExtraBuildComponents;

use crate::one_for_all::traits::birelay::OfaBiRelay;
use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::component::OfaComponents;

impl<Build, Name> DelegateComponent<Name> for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type Delegate = ExtraBuildComponents<OfaComponents>;
}

impl<Build> HasBiRelayType for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type BiRelay = OfaBiRelayWrapper<Build::BiRelay>;

    fn birelay_error(e: <Build::BiRelay as OfaBiRelay>::Error) -> Self::Error {
        Build::birelay_error(e)
    }
}
