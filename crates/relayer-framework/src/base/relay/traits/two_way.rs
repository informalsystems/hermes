use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::types::HasRelayTypes;

pub trait HasTwoWayRelay: HasErrorType {
    type RelayAToB: HasRelayTypes;

    type RelayBToA: HasRelayTypes<
        SrcChain = <Self::RelayAToB as HasRelayTypes>::DstChain,
        DstChain = <Self::RelayAToB as HasRelayTypes>::SrcChain,
        Error = <Self::RelayAToB as HasErrorType>::Error,
    >;

    fn relay_a_to_b(&self) -> &Self::RelayAToB;

    fn relay_b_to_a(&self) -> &Self::RelayBToA;

    fn relay_error(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error;
}
