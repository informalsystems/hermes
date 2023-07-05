use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;

use crate::one_for_all::traits::birelay::OfaBiRelay;
use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;

impl<Build> HasBiRelayType for OfaBuilderWrapper<Build>
where
    Build: OfaBuilder,
{
    type BiRelay = OfaBiRelayWrapper<Build::BiRelay>;

    fn birelay_error(e: <Build::BiRelay as OfaBiRelay>::Error) -> Self::Error {
        Build::birelay_error(e)
    }
}
