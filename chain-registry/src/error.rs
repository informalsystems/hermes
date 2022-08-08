use flex_error::{define_error, TraceError};
use http;
use reqwest;
use serde_json;
use tendermint_rpc;
use tokio::task::JoinError;
use tokio::time::error::Elapsed;

define_error! {
    RegistryError {
        UrlParseError
            {url : String}
            [TraceError<http::Error>]
            |e| {format!("Error when parsing URL : {}", e.url)},

        UriParseError
            {uri : String}
            [TraceError<http::uri::InvalidUri>]
            |e| {format!("Error when parsing URI : {}", e.uri)},

        RequestError
            {url : String}
            [TraceError<reqwest::Error>]
            |e| {format!("Error when requesting : {}", e.url)},

        StatusError
            {url : String, status : u16}
            |e| {format!("Incorrect HTTP response status ({}) for url : {}", e.status, e.url)},

        JsonParseError
            [TraceError <serde_json::Error>]
            |_| {"Error when parsing json".to_string()},

        NoHealthyRpc
            {chain : String}
            |e| {format!("No healthy RPC found for chain : {}", e.chain)},

        NoHealthyGrpc
            {chain : String}
            |e| {format!("No healthy gRPC found for chain : {}", e.chain)},

        RpcConnectError
            {rpc : String}
            [TraceError<tendermint_rpc::Error>]
            |e| {format!("Error when connecting to RPC : {}", e.rpc)},

        NoAssetFound
            {chain_name : String}
            |e| {format!("No asset found for chain : {}", e.chain_name)},

        UnableToBuildWebsocketEndpoint
            {rpc : String}
            [TraceError<http::Error>]
            |e| {format!("Unable to build websocket endpoint for rpc : {}", e.rpc)},

        GrpcEndpointParseError
            {grpc : String}
            [TraceError<http::Error>]
            |e| {format!("Unable to parse grpc endpoint for : {}", e.grpc)},

        GrpcWithoutPort
            {grpc : String}
            |e| {format!("Provided gRPC endpoint without port : {}", e.grpc)},

        JoinError
            {task : String}
            [TraceError<JoinError>]
            |e| {format!("Error when joining task : {}", e.task)},
        RpcConsensusParamsError
            {rpc : String}
            [TraceError<tendermint_rpc::Error>]
            |e| {format!("Unable to fetch consensus params for rpc : {}", e.rpc)},

        RpcStatusError
            {rpc : String}
            [TraceError<tendermint_rpc::Error>]
            |e| {format!("Unable to fetch status for rpc : {}", e.rpc)},

        RpcSyncingError
            {rpc: String}
            |e| {format!("Rpc node out of sync :  {}", e.rpc)},

        UnableToConnectWithGrpc
            |_| {"Unable to connect with grpc".to_string()},

        WebsocketTimeOutError
            {url : String}
            [TraceError<Elapsed>]
            |e| {format!("Unable to connect to websocket : {}", e.url)},

        WebsocketConnectError
            {url : String}
            [TraceError<tendermint_rpc::Error>]
            |e| {format!("Unable to connect to websocket : {}", e.url)},


        WebsocketConnCloseError
            {url : String}
            [TraceError<tendermint_rpc::Error>]
            |e| {format!("Unable to close websocket connection : {}", e.url)},

    }
}
