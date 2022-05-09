use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct TxSearchRequest {
    pub query: String,
    pub prove: bool,
    pub page: String,
    pub per_page: String,
    pub order_by: String,
}

#[derive(Debug, Serialize, Deserialize, sqlx::FromRow)]
struct EventAttribute {
    pub r#type: String,
    pub key: String,
    pub value: String,
}
