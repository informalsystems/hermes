use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;

use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;

impl<Builder> HasBiRelayType for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    type BiRelay = OfaBiRelayWrapper<Builder::BiRelay>;
}
