use async_trait::async_trait;
use basecoin_store::context::ProvableStore;
use std::fmt::Debug;

/// Defines the interface for running a mock Cosmos chain.
#[async_trait]
pub trait BasecoinRunner {
    type Store: ProvableStore + Debug;

    async fn init(&self);

    async fn begin_block(&self);

    async fn commit(&self);
}
