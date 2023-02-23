use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::one_for_all::traits::birelay::OfaBiRelayPreset;
use crate::one_for_all::traits::builder::OfaBuilder;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::one_for_all::types::builder::OfaBuilderWrapper;

impl<Builder, Preset> HasBiRelayType for OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder<Preset = Preset>,
    Preset: OfaBiRelayPreset<Builder::BiRelay>,
{
    type BiRelay = OfaBiRelayWrapper<Builder::BiRelay>;
}
