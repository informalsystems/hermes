use std::net::SocketAddr;

use axum::{routing::post, Extension, Router};
use clap::Parser;
use sqlx::postgres::PgPoolOptions;
use tendermint_rpc::Url;
use tower_http::trace::TraceLayer;
use tracing::info;

use ibc_proxy::{listen::listen, routes};

/// IBC Node
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Port to listen to
    #[clap(long)]
    port: u16,

    /// PostgreSQL database URI
    #[clap(
        long,
        default_value = "postgres://tendermint:tendermint@localhost/tendermint"
    )]
    db: String,

    /// RPC address of the full node to proxy requests to
    #[clap(long, default_value = "http://localhost:26657")]
    rpc: Url,

    /// WebSocket address of the full node to listen for events from
    #[clap(long, default_value = "ws://localhost:26657/websocket")]
    ws: Url,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    color_eyre::install()?;
    logging::setup()?;

    let args = Args::parse();

    info!("Connecting to database");

    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect(&args.db)
        .await?;

    info!("Connecting to WebSocket endpoint");

    tokio::spawn(listen(pool.clone(), args.ws));

    let app = Router::new()
        .route("/", post(routes::root))
        .layer(TraceLayer::new_for_http())
        .layer(Extension(pool))
        .layer(Extension(hyper::client::Client::default()))
        .layer(Extension(args.rpc));

    let addr = SocketAddr::from(([127, 0, 0, 1], args.port));

    info!("Listening on http://{addr}");

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

mod logging {
    use std::error::Error;

    use tracing_error::ErrorLayer;
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter, Registry};

    pub fn setup() -> Result<(), Box<dyn Error>> {
        Registry::default()
            .with(EnvFilter::from_default_env())
            .with(tracing_subscriber::fmt::layer())
            .with(ErrorLayer::default())
            .init();

        Ok(())
    }
}
