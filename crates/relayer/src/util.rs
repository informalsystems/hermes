mod block_on;
pub use block_on::{block_on, spawn_blocking};

pub mod collate;
pub mod compat_mode;
pub mod debug_section;
pub mod diff;
pub mod excluded_sequences;
pub mod iter;
pub mod lock;
pub mod pretty;
pub mod profiling;
pub mod queue;
pub mod retry;
pub mod seq_range;
pub mod stream;
pub mod task;

/// Helper function to create a gRPC client.
pub async fn create_grpc_client<T>(
    grpc_addr: &tonic::transport::Uri,
    client_constructor: impl FnOnce(tonic::transport::Channel) -> T,
) -> Result<T, crate::error::Error> {
    let builder = tonic::transport::Channel::builder(grpc_addr.clone());

    // Don't configures TLS for the endpoint if using IPv6
    let builder = if grpc_addr.scheme() == Some(&http::uri::Scheme::HTTPS) {
        let domain = grpc_addr
            .host()
            .map(|d| d.replace(['[', ']'], ""))
            .ok_or_else(|| crate::error::Error::invalid_http_host(grpc_addr.to_string()))?;
        let tls_config = tonic::transport::ClientTlsConfig::new()
            .with_native_roots()
            .domain_name(domain);
        builder
            .tls_config(tls_config)
            .map_err(crate::error::Error::grpc_transport)?
    } else {
        builder
    };

    let channel = builder
        .connect()
        .await
        .map_err(crate::error::Error::grpc_transport)?;
    Ok(client_constructor(channel))
}
