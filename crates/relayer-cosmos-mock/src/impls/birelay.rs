use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::relay::traits::two_way::HasTwoWayRelay;

use crate::contexts::{birelay::MockCosmosBiRelay, relay::MockCosmosRelay};
use crate::types::error::Error;

impl HasErrorType for MockCosmosBiRelay {
    type Error = Error;
}

impl HasTwoWayRelay for MockCosmosBiRelay {
    type RelayAToB = MockCosmosRelay;

    type RelayBToA = MockCosmosRelay;

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
