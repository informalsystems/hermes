use ibc_relayer_all_in_one::one_for_all::traits::birelay::OfaBiRelayPreset;
use ibc_relayer_all_in_one::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;

use crate::one_for_all::traits::builder::OfaFullBuilder;
use crate::one_for_all::types::builder::OfaFullBuilderWrapper;

impl<Builder, Preset> HasBiRelayType for OfaFullBuilderWrapper<Builder>
where
    Builder: OfaFullBuilder<Preset = Preset>,
    Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    type BiRelay = OfaBiRelayWrapper<Builder::BiRelay>;
}
