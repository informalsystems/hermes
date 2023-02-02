use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::relay::traits::types::HasRelayTypes;
use core::fmt::Debug;

#[derive(Clone)]
pub struct TwoWayRelayContext<RelayAToB, RelayBToA> {
    pub relay_a_to_b: RelayAToB,
    pub relay_b_to_a: RelayBToA,
}

impl<RelayAToB, RelayBToA> TwoWayRelayContext<RelayAToB, RelayBToA> {
    pub fn new(relay_a_to_b: RelayAToB, relay_b_to_a: RelayBToA) -> Self {
        Self {
            relay_a_to_b,
            relay_b_to_a,
        }
    }
}

impl<Error, RelayAToB, RelayBToA> HasErrorType for TwoWayRelayContext<RelayAToB, RelayBToA>
where
    Error: Debug + Async,
    RelayAToB: HasRelayTypes<Error = Error>,
    RelayBToA: HasRelayTypes<Error = Error>,
{
    type Error = Error;
}

impl<Error, RelayAToB, RelayBToA> HasTwoWayRelay for TwoWayRelayContext<RelayAToB, RelayBToA>
where
    Error: Debug + Async,
    RelayAToB: HasRelayTypes<Error = Error>,
    RelayBToA: HasRelayTypes<
        SrcChain = RelayAToB::DstChain,
        DstChain = RelayAToB::SrcChain,
        Error = Error,
    >,
{
    type RelayAToB = RelayAToB;

    type RelayBToA = RelayBToA;

    fn relay_a_to_b(&self) -> &RelayAToB {
        &self.relay_a_to_b
    }

    fn relay_b_to_a(&self) -> &RelayBToA {
        &self.relay_b_to_a
    }

    fn error_a_to_b(e: Error) -> Error {
        e
    }

    fn error_b_to_a(e: Error) -> Error {
        e
    }
}
