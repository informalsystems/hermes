use async_trait::async_trait;

use crate::base::all_for_one::birelay::AfoBaseBiRelay;
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasBiRelayType: Async {
    type BiRelay: AfoBaseBiRelay;
}

#[async_trait]
pub trait CanBuildBiRelay: HasBiRelayType + HasErrorType {
    async fn build_birelay(&self) -> Result<Self::BiRelay, Self::Error>;
}
