use flex_error::{define_error, TraceError};

use tendermint_rpc::Error as RpcError;

define_error! {
    #[derive(Debug, Clone)]
    Error {
        CollectEventsFailed
            { reason: String }
            |e| { format!("failed to extract IBC events: {0}", e.reason) },

        ChannelSendFailed
            |_| { "event monitor: internal message-passing failure: could not send message" },

        ChannelRecvFailed
            |_| { "event monitor: internal message-passing failure: could not receive message" },

        Rpc
            [ TraceError<RpcError> ]
            |_| { "RPC error" },
    }
}
