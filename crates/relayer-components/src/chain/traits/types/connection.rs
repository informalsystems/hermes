use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub enum ConnectionBaseState {
    Init,
    TryOpen,
    Open,
}

pub trait HasConnectionStateType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionState: Async;

    fn connection_base_state(state: &Self::ConnectionState) -> Option<ConnectionBaseState>;
}

pub trait HasInitConnectionOptionsType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type InitConnectionOptions: Async;
}

/**
    Payload that contains necessary counterparty information such as proofs and parameters
    in order for a self chain to build a connection handshake message.
*/
pub trait HasConnectionHandshakePayloads<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionOpenInitPayload: Async;

    type ConnectionOpenTryPayload: Async;

    type ConnectionOpenAckPayload: Async;

    type ConnectionOpenConfirmPayload: Async;
}
