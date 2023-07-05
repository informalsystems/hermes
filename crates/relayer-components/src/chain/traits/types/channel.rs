use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasInitChannelOptionsType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type InitChannelOptions: Async;
}
