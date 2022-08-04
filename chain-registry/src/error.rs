use flex_error::{define_error, TraceError};
use http;
use reqwest;
use serde_json;

define_error! {
    RegistryError {
        UrlParseError
            {chain : String}
            [TraceError<http::Error>]
            |e| {format!("Error when parsing URL for chain : {}", e.chain)},

        RequestError
            {url : String}
            [ TraceError<reqwest::Error>]
            |e| {format!("Error when requesting : {}", e.url)},

        StatusError
            {chain : String, status : u16}
            |e| {format!("Incorrect HTTP response status ({}) for chain : {}", e.status, e.chain)},

        JsonParseError
            {chain : String}
            [TraceError <serde_json::Error>]
            |e| {format!("Error when parsing json for chain : {}", e.chain)},

        }
}
