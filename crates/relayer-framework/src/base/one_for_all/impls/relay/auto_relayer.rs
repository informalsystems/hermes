use async_trait::async_trait;

use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::auto_relayer::{AutoRelayer, CanAutoRelay};
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Preset> CanAutoRelay for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn auto_relay(&self) {
        Preset::AutoRelayer::auto_relay(self).await
    }
}
