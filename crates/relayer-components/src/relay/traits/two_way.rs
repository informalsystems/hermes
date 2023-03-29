use crate::core::traits::error::HasErrorType;
use crate::relay::traits::types::HasRelayTypes;

/// Trait for types that have a two-way relay context, i.e.,
/// those that can relay in both directions between two connected
/// chains.
///
/// Two-way relay contexts are composed of two separate relay
/// contexts, one that relays from chain A to chain B, the
/// other that relays from chain B to chain A.
pub trait HasTwoWayRelay: HasErrorType {
    /// The relay context that relays from chain A to chain B.
    type RelayAToB: HasRelayTypes;

    /// The relay context that relays from chain B to chain A.
    ///
    /// In order to ensure that this relay context is indeed
    /// relaying between the same two chains as the `RelayAToB`
    /// context, we assert that the `RelayBToA` context's source
    /// chain is the `RelayAToB` context's destination chain and
    /// vice versa. In addition, we also assert that both relay
    /// context's have the same error type.
    type RelayBToA: HasRelayTypes<
        SrcChain = <Self::RelayAToB as HasRelayTypes>::DstChain,
        DstChain = <Self::RelayAToB as HasRelayTypes>::SrcChain,
        Error = <Self::RelayAToB as HasErrorType>::Error,
    >;

    /// Returns a read-only reference to the relay context from chain A
    /// to chain B.
    fn relay_a_to_b(&self) -> &Self::RelayAToB;

    /// Returns a read-only reference to the relay context from chain B
    /// to chain A.
    fn relay_b_to_a(&self) -> &Self::RelayBToA;

    /// Converts an error from a one-way relay context into an error from
    /// a two-way relay context.
    fn relay_error(e: <Self::RelayAToB as HasErrorType>::Error) -> Self::Error;
}
