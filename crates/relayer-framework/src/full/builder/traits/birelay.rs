use async_trait::async_trait;

use crate::base::builder::traits::birelay::CanBuildBiRelay;
use crate::base::core::traits::error::HasErrorType;
use crate::full::all_for_one::birelay::AfoFullBiRelay;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAfoFullBiRelay: HasErrorType {
    type AfoFullBiRelay: AfoFullBiRelay;

    async fn build_afo_full_birelay(&self) -> Result<Self::AfoFullBiRelay, Self::Error>;
}

#[async_trait]
impl<Context> CanBuildAfoFullBiRelay for Context
where
    Context: CanBuildBiRelay,
    Context::BiRelay: AfoFullBiRelay,
{
    type AfoFullBiRelay = Context::BiRelay;

    async fn build_afo_full_birelay(&self) -> Result<Context::BiRelay, Context::Error> {
        self.build_birelay().await
    }
}
