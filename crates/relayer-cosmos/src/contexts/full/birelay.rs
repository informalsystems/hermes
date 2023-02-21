use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::traits::birelay::CosmosBiRelay;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::contexts::full::relay::FullCosmosRelay;

pub struct FullCosmosBiRelay<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainA, ChainB>>>,
    pub relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainB, ChainA>>>,
}

impl<ChainA, ChainB> FullCosmosBiRelay<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    pub fn new(
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
        relay_a_to_b: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainA, ChainB>>>,
        relay_b_to_a: OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<ChainB, ChainA>>>,
    ) -> Self {
        Self {
            runtime,
            relay_a_to_b,
            relay_b_to_a,
        }
    }
}

impl<ChainA, ChainB> CosmosBiRelay for FullCosmosBiRelay<ChainA, ChainB>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    type Preset = FullPreset;

    type RelayAToB = FullCosmosRelay<ChainA, ChainB>;

    type RelayBToA = FullCosmosRelay<ChainB, ChainA>;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn relay_a_to_b(&self) -> &OfaRelayWrapper<CosmosRelayWrapper<Self::RelayAToB>> {
        &self.relay_a_to_b
    }

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<CosmosRelayWrapper<Self::RelayBToA>> {
        &self.relay_b_to_a
    }
}
