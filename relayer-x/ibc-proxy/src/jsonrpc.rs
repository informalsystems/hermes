use std::ops::{Deref, DerefMut};

use axum::{
    async_trait,
    body::HttpBody,
    extract::{rejection::JsonRejection, FromRequest, RequestParts},
    http::StatusCode,
    response::{IntoResponse, Response},
    BoxError, Json,
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct JsonRpcRequest<T> {
    pub jsonrpc: String,
    pub method: String,
    pub id: serde_json::Value,
    pub params: T,
}

impl<T> JsonRpcRequest<T> {
    pub fn new(method: String, id: serde_json::Value, params: T) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            method,
            id,
            params,
        }
    }

    pub fn reply_success<U>(self, result: U) -> JsonRpcResponse<U> {
        JsonRpcResponse::success(self.id, result)
    }

    pub fn reply_error<U>(self, error: impl ToString) -> JsonRpcResponse<U> {
        JsonRpcResponse::error(self.id, error)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct JsonRpcResponse<T> {
    jsonrpc: String,
    id: serde_json::Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<T>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

impl<T> JsonRpcResponse<T> {
    pub fn success(id: serde_json::Value, result: T) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            result: Some(result),
            error: None,
            id,
        }
    }

    pub fn error(id: serde_json::Value, msg: impl ToString) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            result: None,
            error: Some(msg.to_string()),
            id,
        }
    }
}

impl<T> IntoResponse for JsonRpcResponse<T>
where
    T: Serialize,
{
    fn into_response(self) -> Response {
        Json(self).into_response()
    }
}

#[non_exhaustive]
pub enum JsonRpcRejection {
    Json(JsonRejection),
    InvalidVersion(String),
}

impl IntoResponse for JsonRpcRejection {
    fn into_response(self) -> Response {
        // TODO: This should return a JSON-RPC response
        match self {
            Self::Json(rejection) => rejection.into_response(),
            Self::InvalidVersion(version) => (
                StatusCode::BAD_REQUEST,
                format!("Invalid JSON-RPC version: {version}"),
            )
                .into_response(),
        }
    }
}

pub type JsonRpc<T> = JsonRpcRequest<T>;

#[async_trait]
impl<T, B> FromRequest<B> for JsonRpc<T>
where
    T: DeserializeOwned,
    B: HttpBody + Send,
    B::Data: Send,
    B::Error: Into<BoxError>,
{
    type Rejection = JsonRpcRejection;

    async fn from_request(req: &mut RequestParts<B>) -> Result<Self, Self::Rejection> {
        let Json(jrpc_req) = Json::<JsonRpcRequest<T>>::from_request(req)
            .await
            .map_err(JsonRpcRejection::Json)?;

        if &jrpc_req.jsonrpc != "2.0" {
            return Err(JsonRpcRejection::InvalidVersion(jrpc_req.jsonrpc));
        }

        Ok(jrpc_req)
    }
}

impl<T> Deref for JsonRpc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.params
    }
}

impl<T> DerefMut for JsonRpc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.params
    }
}
