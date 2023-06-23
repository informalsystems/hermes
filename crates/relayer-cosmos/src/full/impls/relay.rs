use async_trait::async_trait;
use ibc_relayer_all_in_one::extra::one_for_all::traits::relay::OfaFullRelay;

use crate::base::error::Error;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::full::traits::relay::CosmosFullRelay;
use crate::full::types::batch::CosmosBatchSender;

#[async_trait]
impl<Relay> OfaFullRelay for CosmosRelayWrapper<Relay>
where
    Relay: CosmosFullRelay,
{
}
