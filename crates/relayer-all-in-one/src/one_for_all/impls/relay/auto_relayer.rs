use async_trait::async_trait;
use ibc_relayer_components::relay::traits::auto_relayer::{AutoRelayer, CanAutoRelay};

use crate::one_for_all::components;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanAutoRelay for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn auto_relay(&self) -> Result<(), Relay::Error> {
        components::AutoRelayer::auto_relay(self).await
    }
}
