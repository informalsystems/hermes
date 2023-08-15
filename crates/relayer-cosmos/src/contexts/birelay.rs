use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;

use crate::contexts::relay::CosmosRelay;

pub struct CosmosBiRelay<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    pub runtime: TokioRuntimeContext,
    pub relay_a_to_b: OfaRelayWrapper<CosmosRelay<ChainA, ChainB>>,
    pub relay_b_to_a: OfaRelayWrapper<CosmosRelay<ChainB, ChainA>>,
}

impl<ChainA, ChainB> CosmosBiRelay<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    pub fn new(
        runtime: TokioRuntimeContext,
        relay_a_to_b: OfaRelayWrapper<CosmosRelay<ChainA, ChainB>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelay<ChainB, ChainA>>,
    ) -> Self {
        Self {
            runtime,
            relay_a_to_b,
            relay_b_to_a,
        }
    }
}
