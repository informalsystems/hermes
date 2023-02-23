use async_trait::async_trait;
use ibc_relayer_components::relay::traits::auto_relayer::{AutoRelayer, CanAutoRelay};

use crate::base::one_for_all::traits::birelay::{OfaBiRelay, OfaBiRelayPreset};
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<BiRelay, Preset> CanAutoRelay for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: OfaBiRelay<Preset = Preset>,
    Preset: OfaBiRelayPreset<BiRelay>,
{
    async fn auto_relay(&self) {
        Preset::TwoWayAutoRelayer::auto_relay(self).await
    }
}
