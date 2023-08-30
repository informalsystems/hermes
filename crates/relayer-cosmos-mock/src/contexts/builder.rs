use alloc::sync::Arc;
use basecoin_store::impls::InMemoryStore;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use tendermint_testgen::Validator;
use tokio::runtime::Runtime as TokioRuntime;

use super::{basecoin::MockBasecoin, chain::MockCosmosContext, relay::MockCosmosRelay};
use crate::{traits::endpoint::BasecoinEndpoint, types::error::Error};

pub struct MockCosmosBuilder {
    pub runtime: TokioRuntimeContext,
}

impl MockCosmosBuilder {
    pub fn new(runtime: TokioRuntime) -> Self {
        Self {
            runtime: TokioRuntimeContext::new(Arc::new(runtime)),
        }
    }

    pub fn build_chain(
        &mut self,
        chain_id: ChainId,
        validators: Vec<Validator>,
    ) -> Arc<MockBasecoin<InMemoryStore>> {
        let chain = Arc::new(MockBasecoin::new(
            self.runtime.clone(),
            chain_id,
            validators,
            InMemoryStore::default(),
        ));

        chain.run();

        chain
    }

    pub fn build_relay<SrcChain: BasecoinEndpoint, DstChain: BasecoinEndpoint>(
        &self,
        src_chain_ctx: Arc<MockCosmosContext<SrcChain>>,
        dst_chain_ctx: Arc<MockCosmosContext<DstChain>>,
    ) -> Result<MockCosmosRelay<SrcChain, DstChain>, Error> {
        MockCosmosRelay::new(self.runtime.clone(), src_chain_ctx, dst_chain_ctx)
    }
}
