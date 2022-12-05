use flex_error::{define_error, TraceError};

use tendermint_rpc::{Error as RpcError, Url};

use ibc_relayer_types::core::ics24_host::identifier::ChainId;

define_error! {
    #[derive(Debug, Clone)]
    Error {
        WebSocketDriver
            [ TraceError<RpcError> ]
            |_| { "WebSocket driver failed" },

        ClientCreationFailed
            { chain_id: ChainId, address: Url }
            |e| { format!("failed to create WebSocket driver for chain {0} with address {1}", e.chain_id, e.address) },

        ClientTerminationFailed
            [ TraceError<tokio::task::JoinError> ]
            |_| { "failed to terminate previous WebSocket driver" },

        ClientCompletionFailed
            [ TraceError<RpcError> ]
            |_| { "failed to run previous WebSocket driver to completion" },

        ClientSubscriptionFailed
            [ TraceError<RpcError> ]
            |_| { "failed to run previous WebSocket driver to completion" },

        NextEventBatchFailed
            [ TraceError<RpcError> ]
            |_| { "failed to collect events over WebSocket subscription" },

        CollectEventsFailed
            { reason: String }
            |e| { format!("failed to extract IBC events: {0}", e.reason) },

        ChannelSendFailed
            |_| { "event monitor: internal message-passing failure: could not send message" },

        ChannelRecvFailed
            |_| { "event monitor: internal message-passing failure: could not receive message" },

        SubscriptionCancelled
            [ TraceError<RpcError> ]
            |_| { "subscription cancelled" },

        Rpc
            [ TraceError<RpcError> ]
            |_| { "RPC error" },
    }
}

impl Error {
    pub fn canceled_or_generic(e: RpcError) -> Self {
        use tendermint_rpc::error::ErrorDetail;

        match e.detail() {
            ErrorDetail::Server(detail) if detail.reason.contains("subscription was cancelled") => {
                Self::subscription_cancelled(e)
            }
            _ => Self::rpc(e),
        }
    }
}
