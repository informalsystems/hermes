use std::io;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::net::TcpStream;
use tracing_subscriber::filter;
use tracing_subscriber::reload::Handle;

use ibc_relayer::config::TracingServerConfig;

pub type ReloadHandle<S> = Handle<filter::EnvFilter, S>;

pub async fn spawn_reload_handler<S>(
    reload_handle: ReloadHandle<S>,
    config: TracingServerConfig,
) -> io::Result<()> {
    if !config.enabled {
        return Ok(());
    }

    let listener = TcpListener::bind(("0.0.0.0", config.port)).await?;

    loop {
        let (mut socket, _) = listener.accept().await?;

        let mut buffer = String::new();
        socket.read_to_string(&mut buffer).await?;

        let cmd = buffer.trim_end();
        let _ = reload_handle.reload(filter::EnvFilter::new(cmd));
        let success_msg = format!("Successfully set tracing filter to `{}`\n", cmd);
        socket.write_all(success_msg.as_bytes()).await?;
    }
}

pub async fn send_command(cmd: &str, port: u16) -> io::Result<String> {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).await?;

    stream.write_all(cmd.as_bytes()).await?;

    let mut buffer = String::new();
    stream.read_to_string(&mut buffer).await?;

    Ok(buffer)
}
