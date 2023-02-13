use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::birelay::OfaBiRelay;
use crate::base::one_for_all::types::birelay::OfaBiRelayWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::two_way::HasTwoWayRelay;

impl<BiRelay> HasTwoWayRelay for OfaBiRelayWrapper<BiRelay>
where
    BiRelay: OfaBiRelay,
{
    type RelayAToB = OfaRelayWrapper<BiRelay::RelayAToB>;

    type RelayBToA = OfaRelayWrapper<BiRelay::RelayBToA>;

    fn relay_a_to_b(&self) -> &Self::RelayAToB {
        self.birelay.relay_a_to_b()
    }

    fn relay_b_to_a(&self) -> &Self::RelayBToA {
        self.birelay.relay_b_to_a()
    }

    fn error_a_to_b(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error {
        BiRelay::error_a_to_b(e)
    }

    fn error_b_to_a(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error {
        BiRelay::error_b_to_a(e)
    }
}
