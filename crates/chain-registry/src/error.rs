use flex_error::{define_error, TraceError};
use http;
use reqwest;
use serde_json;
use std::path::PathBuf;
use tendermint_rpc;
use tokio::task::JoinError;
use tokio::time::error::Elapsed;

define_error! {
    RegistryError {

        GrpcEndpointParseError
            { grpc: String }
            [ TraceError<http::Error> ]
            |e| { format_args!("Unable to parse gRPC endpoint for: {}", e.grpc) },

        JoinError
            { task: String }
            [ TraceError<JoinError> ]
            |e| { format_args!("Error when joining task: {}", e.task) },

        JsonParseError
            { chain_name: String }
            [ TraceError <serde_json::Error> ]
            |e| { format_args!("Error when parsing JSON for chain {}", e.chain_name) },

        NoAssetFound
            { chain_name: String }
            |e| { format_args!("No asset found for chain: {}", e.chain_name) },

        NoHealthyGrpc
            { chain: String }
            |e| { format_args!("No healthy gRPC found for chain: {}", e.chain) },

        NoHealthyRpc
            { chain: String }
            |e| { format_args!("No healthy RPC found for chain: {}", e.chain) },

        PathError
            { path: PathBuf}
            |e| { format_args!("Error when parsing path: {:?}", e.path) },

        RequestError
            { url: String }
            [ TraceError<reqwest::Error> ]
            |e| { format_args!("Error when requesting: {}", e.url) },

        RpcConnectError
            { rpc: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Error when connecting to RPC: {}", e.rpc) },

        RpcConsensusParamsError
            { rpc: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Unable to fetch consensus params for RPC: {}", e.rpc) },

        RpcStatusError
            { rpc: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Unable to fetch status for RPC: {}", e.rpc) },

        RpcUrlWithoutAuthority
            { rpc: String }
            |e| { format_args!("Provided RPC URL without authority: {}", e.rpc) },

        RpcSyncingError
            { rpc: String }
            |e| { format_args!("Rpc node out of sync: {}", e.rpc) },

        UriParseError
            { uri: String }
            [ TraceError<http::uri::InvalidUri> ]
            |e| { format_args!("Error when parsing URI: {}", e.uri) },

        UrlParseError
            { url: String }
            [ TraceError<http::Error> ]
            |e| { format_args!("Error when parsing URL: {}", e.url) },

        TendermintUrlParseError
            { url: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Error when parsing URL: {}", e.url) },

        WebsocketUrlParseError
            { url: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Error when parsing URL: {}", e.url) },

        StatusError
            { url: String, status : u16}
            |e| { format_args!("Incorrect HTTP response status ({}) for URL: {}", e.status, e.url) },

        UnableToBuildWebsocketEndpoint
            { rpc: String }
            [ TraceError<http::Error> ]
            |e| { format_args!("Unable to build WebSocket endpoint for RPC: {}", e.rpc) },

        UnableToConnectWithGrpc
            |_| { "Unable to connect with gRPC" },

        WebsocketConnectError
            { url: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Unable to connect to WebSocket: {}", e.url) },

        WebsocketConnCloseError
            { url: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Unable to close WebSocket connection: {}", e.url) },

        WebsocketTimeOutError
            { url: String }
            [ TraceError<Elapsed> ]
            |e| { format_args!("Unable to connect to WebSocket: {}", e.url) },

        WebsocketDriverError
            { url: String }
            [ TraceError<tendermint_rpc::Error> ]
            |e| { format_args!("Unable to close WebSocket driver: {}", e.url) },
    }
}
