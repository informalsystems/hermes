use alloc::string::String;
use alloc::sync::Arc;

use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc_relayer_runtime::types::error::Error as TokioError;

pub type Error = Arc<BaseError>;

define_error! {
    #[derive(Clone, Debug)]
    BaseError {
        EmptyIterator
            | _ | { "empty iterator error" },

        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        Tokio
            [ TokioError ]
            | _ | { "tokio runtime error" },

        MismatchError
            { expected: usize, actual: usize }
            | e | {
                format_args!("mismatch size for events returned. expected: {}, got: {}",
                    e.expected, e.actual)
            },

        NoChainState
        { id: String, height: u128 }
            | e | {
                format_args!("no chain state found for chain: {} at height {}", e.id, e.height)
            },

        NoConsensusState
        { id: String }
            | e | {
                format_args!("no consensus state found for client: {}", e.id)
            },

        NoConsensusStateAtHeight
        { id: String, height: u128 }
            | e | {
                format_args!("no consensus state found for client {} at height {}", e.id, e.height)
            },

        ConsensusDivergence
        { id: String, height: u128 }
            | e | {
                format_args!("trying to insert different consensus states for client {} at height {}", e.id, e.height)
            },

        ReceiveWithoutSent
        { chain: String, channel_id: String }
            | e | {
                format_args!("error trying to build RecvPacket from chain `{}` with channel ID `{}`. Source chain Consensus State doesn't have the packet recorded as sent", e.chain, e.channel_id)
            },

        AcknowledgmentWithoutReceived
        { chain: String, channel_id: String }
            | e | {
                format_args!("error trying to build AckPacket from chain `{}` with channel ID `{}`. Destination chain Consensus State doesn't have the packet recorded as received", e.chain, e.channel_id)
            },

        TimeoutWithoutSent
        { chain: String, channel_id: String }
            | e | {
                format_args!("error trying to build TimeoutPacket from chain `{}` with channel ID `{}`. Source chain Consensus State doesn't have the packet recorded as sent", e.chain, e.channel_id)
            },

        TimeoutReceive
        { chain: String, height: u128, chain_height: u128, timestamp: u128, current_timestamp: u128 }
            | e | {
                format_args!("error receiving RecvPacket for chain {}. Packet timeout height {}, chain height {}. Packet timeout timestamp {}, current timestamp {}", e.chain, e.height, e.chain_height, e.timestamp, e.current_timestamp)
            },

        NoClientForChannel
        { channel_id: String, chain: String }
            | e | { format_args!("error no client mapped to the channel `{}` for chain `{}`", e.channel_id, e.chain) },
    }
}

impl From<Report> for BaseError {
    fn from(e: Report) -> Self {
        BaseError::generic(e)
    }
}
