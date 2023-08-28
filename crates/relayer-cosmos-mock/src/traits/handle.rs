use async_trait::async_trait;
use std::fmt::Debug;

use basecoin_app::modules::ibc::Ibc;
use basecoin_store::context::ProvableStore;
use basecoin_store::impls::RevertibleStore;
use ibc::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::path::Path;
use ibc::Height;
use ibc_relayer_components::core::traits::sync::Async;
use tendermint_testgen::light_block::TmLightBlock;

use crate::types::error::Error;

#[async_trait]
pub trait BasecoinHandle: Async + Clone {
    type Store: ProvableStore + Debug;

    fn chain_id(&self) -> &ChainId;

    fn ibc(&self) -> Ibc<RevertibleStore<Self::Store>>;

    fn blocks(&self) -> Vec<TmLightBlock>;

    fn grow_blocks(&self);

    async fn init(&self);

    async fn begin_block(&self);

    async fn commit(&self);

    async fn run(&self);

    async fn query(
        &self,
        path: impl Into<Path> + Send,
        height: &Height,
    ) -> Result<(Vec<u8>, CommitmentProofBytes), Error>;
}
