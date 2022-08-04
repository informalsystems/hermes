use flex_error::{define_error, TraceError};
use http;
use reqwest;
use serde_json;
use tendermint_rpc;

define_error! {
    RegistryError {
        UrlParseError
            {url : String}
            [TraceError<http::Error>]
            |e| {format!("Error when parsing URL : {}", e.url)},

        RequestError
            {url : String}
            [TraceError<reqwest::Error>]
            |e| {format!("Error when requesting : {}", e.url)},

        StatusError
            {url : String, status : u16}
            |e| {format!("Incorrect HTTP response status ({}) for url : {}", e.status, e.url)},

        JsonParseError
            [TraceError <serde_json::Error>]
            |_| {format!("Error when parsing json")},

        NoHealthyRpc
            |_| {format!("No healthy RPC found")},

        NoHealthyGrpc
            |_| {format!("No healthy GRPC found")},
        
        RpcConnectErrror
            {rpc : String}
            [TraceError<tendermint_rpc::Error>]
            |e| {format!("Error when connecting to RPC : {}", e.rpc)},
        
        NoAssetFound
            {chain_name : String}
            |e| {format!("No asset found for chain : {}", e.chain_name)},	
        
        UnableToBuildWebSocketEndpoint
            {rpc : String}
            [TraceError<http::Error>]
            |e| {format!("Unable to build websocket endpoint for rpc : {}", e.rpc)},
        
        GrpcEndpointParseError
            {grpc : String}
            [TraceError<http::Error>]
            |e| {format!("Unable to parse grpc endpoint for : {}", e.grpc)},


        }
}
