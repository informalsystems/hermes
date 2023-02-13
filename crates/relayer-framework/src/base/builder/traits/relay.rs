use async_trait::async_trait;

use crate::base::builder::types::aliases::{RelayAToB, RelayBToA};
use crate::base::core::traits::error::HasErrorType;
use crate::std_prelude::*;

use super::birelay::HasBiRelayType;

#[async_trait]
pub trait CanBuildRelayAToB: HasBiRelayType + HasErrorType {
    async fn build_relay_a_to_b(&self) -> Result<RelayAToB<Self>, Self::Error>;
}

#[async_trait]
pub trait CanBuildRelayBToA: HasBiRelayType + HasErrorType {
    async fn build_relay_b_to_a(&self) -> Result<RelayBToA<Self>, Self::Error>;
}
