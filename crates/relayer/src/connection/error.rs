use core::time::Duration;
use flex_error::define_error;
use ibc::core::ics03_connection::connection::{Counterparty, State};
use ibc::core::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::events::IbcEvent;

use crate::error::Error as RelayerError;
use crate::foreign_client::{ForeignClientError, HasExpiredOrFrozenError};
use crate::supervisor::Error as SupervisorError;

define_error! {
    ConnectionError {
        Relayer
            [ RelayerError ]
            |e| { format_args!("relayer error: {}", e.source) },

        MissingLocalConnectionId
            |_| { "failed due to missing local connection id" },

        MissingCounterpartyConnectionIdField
            { counterparty: Counterparty }
            |e| {
                format!("the connection end has no connection id field in the counterparty: {:?}",
                    e.counterparty)
            },

        MissingCounterpartyConnectionId
            |_| { "failed due to missing counterparty connection id" },

        ChainQuery
            { chain_id: ChainId }
            [ RelayerError ]
            |e| {
                format!("failed during a query to chain id {0}", e.chain_id)
            },

        ConnectionQuery
            { connection_id: ConnectionId }
            [ RelayerError ]
            |e| {
                format!("failed to query the connection for {}", e.connection_id)
            },

        ClientOperation
            {
                client_id: ClientId,
                chain_id: ChainId,
            }
            [ ForeignClientError ]
            |e| {
                format!("failed during an operation on client '{0}' hosted by chain '{1}'",
                    e.client_id, e.chain_id)
            },

        Submit
            { chain_id: ChainId }
            [ RelayerError ]
            |e| {
                format!("failed during a transaction submission step to chain '{0}'",
                    e.chain_id)
            },

        HandshakeFinalize
            |_| { "continue handshake" },

        MaxDelayPeriod
            {
                delay_period: Duration,
                max_delay_period: Duration
            }
            |e| {
                format!("invalid delay period '{:?}': should be at max '{:?}'",
                    e.delay_period, e.max_delay_period)
            },

        InvalidEvent
            { event: IbcEvent }
            |e| {
                format!("a connection object cannot be built from {}",
                    e.event)
            },

        RetryInternal
            { reason: String }
            | e | {
                format_args!("encountered internal error during retry: {}",
                    e.reason)
            },

        TxResponse
            { event: String }
            |e| {
                format!("tx response event consists of an error: {}",
                    e.event)
            },

        ConnectionClientIdMismatch
            {
                client_id: ClientId,
                foreign_client_id: ClientId
            }
            |e| {
                format!("the client id ({}) in the connection end does not match the foreign client id ({})",
                    e.client_id, e.foreign_client_id)
            },

        ChainIdMismatch
            {
                source_chain_id: ChainId,
                destination_chain_id: ChainId
            }
            |e| {
                format!("the source chain of client a ({}) does not not match the destination chain of client b ({})",
                    e.source_chain_id, e.destination_chain_id)
            },

        ConnectionNotOpen
            {
                state: State,
            }
            |e| {
                format!("the connection end is expected to be in state 'Open'; found state: {:?}",
                    e.state)
            },

        Supervisor
            [ SupervisorError ]
            |_| { "supervisor error" },

        MissingConnectionId
            {
                chain_id: ChainId,
            }
            |e| {
                format!("missing connection on source chain {}",
                    e.chain_id)
            },

        Signer
            { chain_id: ChainId }
            [ RelayerError ]
            |e| {
                format!("failed while fetching the signer for chain ({})",
                    e.chain_id)
            },

        MissingConnectionIdFromEvent
            |_| { "cannot extract connection_id from result" },

        MissingConnectionInitEvent
            |_| { "no conn init event was in the response" },

        MissingConnectionTryEvent
            |_| { "no conn try event was in the response" },

        MissingConnectionAckEvent
            |_| { "no conn ack event was in the response" },

        MissingConnectionConfirmEvent
            |_| { "no conn confirm event was in the response" },

        ConnectionProof
            [ RelayerError ]
            |_| { "failed to build connection proofs" },

        ConnectionAlreadyExists
            { connection_id: ConnectionId }
            |e| {
                format!("connection {} already exists in an incompatible state", e.connection_id)
            },

        MaxRetry
            {
                description: String,
                tries: u64,
                total_delay: Duration,
            }
            | e | {
                format_args!("Error after maximum retry of {} and total delay of {}s: {}",
                    e.tries, e.total_delay.as_secs(), e.description)
            },

    }
}

impl HasExpiredOrFrozenError for ConnectionErrorDetail {
    fn is_expired_or_frozen_error(&self) -> bool {
        match self {
            Self::ClientOperation(e) => e.source.is_expired_or_frozen_error(),
            _ => false,
        }
    }
}

impl HasExpiredOrFrozenError for ConnectionError {
    fn is_expired_or_frozen_error(&self) -> bool {
        self.detail().is_expired_or_frozen_error()
    }
}
