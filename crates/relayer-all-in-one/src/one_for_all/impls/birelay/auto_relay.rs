use async_trait::async_trait;
use ibc_relayer_components::relay::traits::auto_relayer::{AutoRelayer, CanAutoRelay};

use crate::one_for_all::components;
use crate::one_for_all::traits::birelay::OfaBiRelay;
use crate::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<BiRelay> CanAutoRelay for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: OfaBiRelay,
{
    async fn auto_relay(&self) -> Result<(), BiRelay::Error> {
        components::TwoWayAutoRelayer::auto_relay(self).await
    }
}
