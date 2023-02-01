use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::types::HasRelayTypes;

pub trait HasTwoWayRelay: HasErrorType {
    type RelayAToB: HasRelayTypes;

    type RelayBToA: HasRelayTypes<
        SrcChain = <Self::RelayAToB as HasRelayTypes>::DstChain,
        DstChain = <Self::RelayAToB as HasRelayTypes>::SrcChain,
    >;

    fn relay_a_to_b(&self) -> &Self::RelayAToB;

    fn relay_b_to_a(&self) -> &Self::RelayBToA;

    fn error_a_to_b(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error;

    fn error_b_to_a(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error;
}
