use ibc_relayer_all_in_one::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::traits::relay::CosmosRelay;
use crate::base::types::relay::CosmosRelayWrapper;

pub trait CosmosBiRelay: Async {
    type Preset: Async;

    type RelayAToB: CosmosRelay<Preset = Self::Preset>;

    type RelayBToA: CosmosRelay<
        Preset = Self::Preset,
        SrcChain = <Self::RelayAToB as CosmosRelay>::DstChain,
        DstChain = <Self::RelayAToB as CosmosRelay>::SrcChain,
    >;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext>;

    fn relay_a_to_b(&self) -> &OfaRelayWrapper<CosmosRelayWrapper<Self::RelayAToB>>;

    fn relay_b_to_a(&self) -> &OfaRelayWrapper<CosmosRelayWrapper<Self::RelayBToA>>;
}
