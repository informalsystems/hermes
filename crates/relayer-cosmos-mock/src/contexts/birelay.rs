use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use std::sync::Arc;

use super::relay::MockCosmosRelay;

pub struct MockCosmosBiRelay {
    pub runtime: TokioRuntimeContext,
    pub relay_a_to_b: Arc<MockCosmosRelay>,
    pub relay_b_to_a: Arc<MockCosmosRelay>,
}

impl MockCosmosBiRelay {
    pub fn new(
        runtime: TokioRuntimeContext,
        relay_a_to_b: Arc<MockCosmosRelay>,
        relay_b_to_a: Arc<MockCosmosRelay>,
    ) -> Self {
        Self {
            runtime,
            relay_a_to_b,
            relay_b_to_a,
        }
    }

    pub fn relay_a_to_b(&self) -> &Arc<MockCosmosRelay> {
        &self.relay_a_to_b
    }

    pub fn relay_b_to_a(&self) -> &Arc<MockCosmosRelay> {
        &self.relay_b_to_a
    }
}
