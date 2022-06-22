use async_trait::async_trait;
use ibc::Height;

use super::context::RelayContext;
use crate::tagged::MonoTagged;

#[async_trait]
pub trait LatestHeightQuerier: RelayContext {
    async fn query_latest_source_height(
        &self,
    ) -> Result<MonoTagged<Self::SrcChain, Height>, Self::Error>;

    async fn query_latest_destination_height(
        &self,
    ) -> Result<MonoTagged<Self::DstChain, Height>, Self::Error>;
}
