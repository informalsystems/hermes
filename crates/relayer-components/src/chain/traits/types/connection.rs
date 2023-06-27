use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasConnectionVersionType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionVersion: Async;
}
