use alloc::sync::Arc;

use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use ibc_relayer::spawn::SpawnError;
use ibc_relayer::supervisor::error::Error as SupervisorError;
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_types::core::ics02_client::error::Error as ClientError;
use ibc_relayer_types::core::ics04_channel::error::Error as ChannelError;
use ibc_relayer_types::core::ics23_commitment;
use ibc_relayer_types::proofs::ProofError;
use prost::EncodeError;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::Error as TendermintRpcError;
use tokio::task::JoinError;
use tonic::transport::Error as TransportError;
use tonic::Status as GrpcStatus;

pub type Error = Arc<BaseError>;

define_error! {
    #[derive(Debug)]
    BaseError {
        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        Tokio
            [ TokioError ]
            | _ | { "tokio runtime error" },

        Channel
            [ ChannelError ]
            | _ | { "channel error" },

        Relayer
            [ RelayerError ]
            | _ | { "ibc-relayer error" },

        ForeignClient
            [ ForeignClientError ]
            | _ | { "foreign client error" },

        Spawn
            [ SpawnError ]
            | _ | { "failed to spawn chain runtime" },

        Supervisor
            [ SupervisorError ]
            | _ | { "supervisor error" },

        Encode
            [ TraceError<EncodeError> ]
            | _ | { "protobuf encode error" },

        Ics23
            [ ics23_commitment::error::Error ]
            | _ | { "ICS23 error" },

        Proofs
            [ ProofError ]
            | _ | { "proofs error" },

        TendermintRpc
            [ TendermintRpcError ]
            | _ | { "tendermint rpc error" },

        MismatchConsensusState
            | _ | { "consensus state of a cosmos chain on the counterparty chain must be a tendermint consensus state" },

        MismatchEventType
            { expected: String, actual: String }
            | e | { format_args!("mismatch event type, expected: {}, actual: {}", e.expected, e.actual) },

        TxNoResponse
            { tx_hash: TxHash }
            | e | { format_args!("failed to receive tx response for tx hash: {}", e.tx_hash) },

        MissingSimulateGasInfo
            | _ | { "missing gas info returned from send_tx_simulate" },

        MissingSendPacket
            | _ | { "missing send packet" },

        CheckTx
            { response: Response }
            | e | { format_args!("check tx error: {:?}", e.response) },

        Join
            [ TraceError<JoinError> ]
            | _ | { "error joining tokio tasks" },

        GrpcTransport
            [ TraceError<TransportError> ]
            |_| { "error in underlying transport when making gRPC call" },

        GrpcStatus
            { status: GrpcStatus, query: String }
            |e| { format!("gRPC call `{}` failed with status: {1}", e.query, e.status) },

        MissingHeight
            { query: String }
            | e | { format_args!("height from query `{}` is missing", e.query) },

        Ics02
            [ ClientError ]
            |e| { format!("ICS 02 error: {}", e.source) },
    }
}
