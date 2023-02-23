use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;

use crate::base::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::extra::one_for_all::traits::builder::OfaFullBuilder;
use crate::extra::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder, Preset> HasBiRelayType for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder<Preset = Preset>,
    Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    type BiRelay = OfaBiRelayWrapper<Builder::BiRelay>;
}
