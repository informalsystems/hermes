use async_trait::async_trait;
use basecoin_store::context::ProvableStore;
use std::fmt::Debug;

#[async_trait]
pub trait BasecoinHandle {
    type Store: ProvableStore + Debug;

    async fn init(&self);

    async fn begin_block(&self);

    async fn commit(&self);
}
