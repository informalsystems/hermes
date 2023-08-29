use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use std::sync::Arc;

use super::relay::MockCosmosRelay;
use crate::traits::endpoint::BasecoinEndpoint;

/// Bi-directional relayer for relaying between
/// [`crates::relayer-cosmos-mock::contexts::MockCosmosRelay`]s
pub struct MockCosmosBiRelay<SrcChain: BasecoinEndpoint, DstChain: BasecoinEndpoint> {
    pub runtime: TokioRuntimeContext,
    pub relay_a_to_b: Arc<MockCosmosRelay<SrcChain, DstChain>>,
    pub relay_b_to_a: Arc<MockCosmosRelay<DstChain, SrcChain>>,
}

impl<SrcChain: BasecoinEndpoint, DstChain: BasecoinEndpoint> MockCosmosBiRelay<SrcChain, DstChain> {
    pub fn new(
        runtime: TokioRuntimeContext,
        relay_a_to_b: Arc<MockCosmosRelay<SrcChain, DstChain>>,
        relay_b_to_a: Arc<MockCosmosRelay<DstChain, SrcChain>>,
    ) -> Self {
        Self {
            runtime,
            relay_a_to_b,
            relay_b_to_a,
        }
    }

    pub fn relay_a_to_b(&self) -> &Arc<MockCosmosRelay<SrcChain, DstChain>> {
        &self.relay_a_to_b
    }

    pub fn relay_b_to_a(&self) -> &Arc<MockCosmosRelay<DstChain, SrcChain>> {
        &self.relay_b_to_a
    }
}
