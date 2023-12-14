use std::{
    error::Error,
    net::SocketAddr,
    sync::Arc,
};

use axum::{
    extract::Query,
    response::IntoResponse,
    routing::get,
    Extension,
    Router,
};
use prometheus::{
    Encoder,
    TextEncoder,
};

use crate::{
    encoder::JsonEncoder,
    state::TelemetryState,
};

#[derive(Copy, Clone, Debug, Default, serde::Deserialize)]
enum Format {
    #[serde(rename = "text")]
    #[default]
    Text,

    #[serde(rename = "json")]
    Json,
}

#[derive(Copy, Clone, Debug, serde::Deserialize)]
struct Metrics {
    format: Option<Format>,
}

pub async fn listen(
    addr: SocketAddr,
    state: Arc<TelemetryState>,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    let app = Router::new()
        .route("/metrics", get(get_metrics))
        .layer(Extension(state));

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

async fn get_metrics(
    Extension(state): Extension<Arc<TelemetryState>>,
    Query(query): Query<Metrics>,
) -> impl IntoResponse {
    match query.format.unwrap_or_default() {
        Format::Text => {
            let encoder = TextEncoder::new();
            let mut buffer = Vec::new();
            encoder.encode(&state.gather(), &mut buffer).unwrap();

            ([("content-type", "text/plain; charset=utf-8")], buffer)
        }
        Format::Json => {
            let encoder = JsonEncoder::new();
            let mut buffer = Vec::new();
            encoder.encode(&state.gather(), &mut buffer).unwrap();

            (
                [("content-type", "application/javascript; charset=utf-8")],
                buffer,
            )
        }
    }
}
