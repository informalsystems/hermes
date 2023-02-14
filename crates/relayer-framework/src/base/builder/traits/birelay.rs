use async_trait::async_trait;

use crate::base::all_for_one::birelay::AfoBaseBiRelay;
use crate::base::builder::types::aliases::{RelayAToB, RelayBToA};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::std_prelude::*;

pub trait HasBiRelayType: Async {
    type BiRelay: HasTwoWayRelay;
}

#[async_trait]
pub trait CanBuildBiRelay: HasBiRelayType + HasErrorType {
    async fn build_birelay(&self) -> Result<Self::BiRelay, Self::Error>;
}

#[async_trait]
pub trait BiRelayBuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_birelay(builder: &Builder) -> Result<Builder::BiRelay, Builder::Error>;
}

#[async_trait]
pub trait CanBuildBiRelayFromRelays: HasBiRelayType + HasErrorType {
    async fn build_birelay_from_relays(
        &self,
        relay_a_to_b: RelayAToB<Self>,
        relay_b_to_a: RelayBToA<Self>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

#[async_trait]
pub trait CanBuildAfoBaseBiRelay:
    HasBiRelayType<BiRelay = Self::AfoBaseBiRelay> + HasErrorType
{
    type AfoBaseBiRelay: AfoBaseBiRelay;

    async fn build_afo_base_birelay(&self) -> Result<Self::AfoBaseBiRelay, Self::Error>;
}

#[async_trait]
impl<Context> CanBuildAfoBaseBiRelay for Context
where
    Context: CanBuildBiRelay,
    Context::BiRelay: AfoBaseBiRelay,
{
    type AfoBaseBiRelay = Context::BiRelay;

    async fn build_afo_base_birelay(&self) -> Result<Self::BiRelay, Self::Error> {
        self.build_birelay().await
    }
}
