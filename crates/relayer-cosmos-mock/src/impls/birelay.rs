use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;

use crate::contexts::{birelay::MockCosmosBiRelay, relay::MockCosmosRelay};
use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;

impl<SrcChain: BasecoinEndpoint, DstChain: BasecoinEndpoint> HasErrorType
    for MockCosmosBiRelay<SrcChain, DstChain>
{
    type Error = Error;
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
