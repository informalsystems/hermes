use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasClientStateType<Counterparty>: HasIbcChainTypes<Counterparty> {
    /**
        The client state of the `Self` chain's client on the `Counterparty` chain
    */
    type ClientState: Async;
}
