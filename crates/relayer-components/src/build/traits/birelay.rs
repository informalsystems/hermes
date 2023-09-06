use crate::core::traits::error::HasErrorType;
use crate::relay::traits::two_way::HasTwoWayRelay;

/// Trait for types that have access to a bi-directional relayer
/// that can relay between two connected chains in both directions.
pub trait HasBiRelayType: HasErrorType {
    /// A relay context that can relay between two chains in a bi-
    /// directional fashion.
    type BiRelay: HasTwoWayRelay;

    fn birelay_error(e: <Self::BiRelay as HasErrorType>::Error) -> Self::Error;
}
