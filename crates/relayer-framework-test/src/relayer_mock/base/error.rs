use alloc::string::String;
use eyre::Report;
use flex_error::{define_error, TraceError};

use ibc_relayer_runtime::tokio::error::Error as TokioError;

define_error! {
    #[derive(Clone, Debug)]
    Error {
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
        { src_chain: String, dst_chain: String }
            | e | {
                format_args!("error trying to build RecvPacket from chain `{}` to `{}`. Source chain Consensus State doesn't have the packet recorded as sent", e.src_chain, e.dst_chain)
            },

        AcknowledgmentWithoutReceived
        { src_chain: String, dst_chain: String }
            | e | {
                format_args!("error trying to build AckPacket from chain `{}` to `{}`. Destination chain Consensus State doesn't have the packet recorded as received", e.dst_chain, e.src_chain)
            },

        TimeoutWithoutSent
        { src_chain: String, dst_chain: String }
            | e | {
                format_args!("error trying to build TimeoutPacket from chain `{}` to `{}`. Source chain Consensus State doesn't have the packet recorded as sent", e.dst_chain, e.src_chain)
            },

        TimeoutReceive
        { chain: String, height: u128, chain_height: u128, timestamp: u128, current_timestamp: u128 }
            | e | {
                format_args!("error receiving RecvPacket for chain {}. Packet timeout height {}, chain height {}. Packet timeout timestamp {}, current timestamp {}", e.chain, e.height, e.chain_height, e.timestamp, e.current_timestamp)
            },
    }
}

impl From<Report> for Error {
    fn from(e: Report) -> Self {
        Error::generic(e)
    }
}
