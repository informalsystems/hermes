use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;

use crate::contexts::{birelay::MockCosmosBiRelay, relay::MockCosmosRelay};
use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;

impl<SrcChain, DstChain> HasErrorType for MockCosmosBiRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type Error = Error;
}

impl<SrcChain, DstChain> HasRuntime for MockCosmosBiRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type Runtime = TokioRuntimeContext;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Self::Error {
        Error::source(e)
    }
}

impl<SrcChain, DstChain> HasTwoWayRelay for MockCosmosBiRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type RelayAToB = MockCosmosRelay<SrcChain, DstChain>;

    type RelayBToA = MockCosmosRelay<DstChain, SrcChain>;

    fn relay_a_to_b(&self) -> &Self::RelayAToB {
        self.relay_a_to_b()
    }

    fn relay_b_to_a(&self) -> &Self::RelayBToA {
        self.relay_b_to_a()
    }

    fn relay_error(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error {
        Error::source(e)
    }
}
