use core::time::Duration;

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

/**
    Payload that contains necessary counterparty information such as proofs and parameters
    in order for a self chain to build a connection handshake message.
*/
pub trait HasConnectionHandshakePayloads<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionInitPayload: Async;

    type ConnectionOpenTryPayload: Async;

    type ConnectionOpenAckPayload: Async;

    type ConnectionOpenConfirmPayload: Async;
}

pub trait HasConnectionVersionType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionVersion: Eq + Default + Async;
}

pub trait HasConnectionDetailsType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionDetails: Async;
}

pub trait HasConnectionDetailsFields<Counterparty>:
    HasConnectionDetailsType<Counterparty>
    + HasConnectionStateType<Counterparty>
    + HasConnectionVersionType<Counterparty>
{
    fn connection_details_state(connection: &Self::ConnectionDetails) -> &Self::ConnectionState;

    fn connection_details_delay(connection: &Self::ConnectionDetails) -> Duration;

    fn connection_details_versions(
        connection: &Self::ConnectionDetails,
    ) -> &[Self::ConnectionVersion];
}
