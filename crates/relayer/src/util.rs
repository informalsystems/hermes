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
    let tls_config = tonic::transport::ClientTlsConfig::new().with_native_roots();
    let builder = tonic::transport::Channel::builder(grpc_addr.clone());

    // Don't configures TLS for the endpoint if using IPv6
    let builder = if is_ipv6(grpc_addr) {
        builder
    } else {
        builder
            .tls_config(tls_config)
            .map_err(crate::error::Error::grpc_transport)?
    };
    let channel = builder
        .connect()
        .await
        .map_err(crate::error::Error::grpc_transport)?;
    Ok(client_constructor(channel))
}

fn is_ipv6(uri: &tonic::transport::Uri) -> bool {
    if let Some(host) = uri.host() {
        host.starts_with('[') && host.ends_with(']')
    } else {
        false
    }
}
