#![forbid(unsafe_code)]
#![deny(
    warnings,
    missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications,
    rust_2018_idioms
)]

//! Read the relayer configuration into the Config struct, in examples for now
//! to support ADR validation..should move to relayer/src soon

use serde_derive::Deserialize;
use std::path::Path;

mod error {
    use anomaly::{BoxError, Context};
    use thiserror::Error;

    pub type Error = anomaly::Error<Kind>;

    /// Various errors related to the configuration handling.
    #[derive(Clone, Debug, Error)]
    pub enum Kind {
        /// An I/O error happened when reading the config file
        #[error("could not read config file")]
        Io,

        /// The configuration file contains invalid TOML
        #[error("invalid TOML config")]
        InvalidConfig,
    }

    impl Kind {
        pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
            Context::new(self, Some(source.into()))
        }
    }
}

#[derive(Debug, Default, Deserialize)]
struct Config {
    timeout: Option<String>,  // use "10s" as default
    strategy: Option<String>, // use "naive" as default
    chains: Vec<ChainConfig>,
    connections: Option<Vec<Connection>>, // use all for default
}

#[derive(Debug, Deserialize)]
struct ChainConfig {
    id: String,
    rpc_addr: Option<String>, // use "http://localhost:26657" as default
    account_prefix: String,
    key_name: String,
    client_ids: Vec<String>,
    gas: Option<u64>, // use 200000 as default
}

#[derive(Debug, Deserialize)]
struct Connection {
    src: Option<ConnectionEnd>,    // use any source
    dest: Option<ConnectionEnd>,   // use any destination
    paths: Option<Vec<RelayPath>>, // use any port, direction bidirectional
}

#[derive(Debug, Deserialize)]
struct ConnectionEnd {
    client_id: String,
    connection_id: Option<String>, // use all connections to this client
}

#[derive(Debug, Deserialize)]
struct RelayPath {
    src_port: Option<String>,  // default from any source port
    dest_port: Option<String>, // default from any dest port
    direction: Option<String>, // default bidirectional
}

/// Attempt to load and parse the config file into the Config struct.
///
/// TODO: If a file cannot be found, return a default Config allowing relayer
///       to relay everything from any to any chain(?)
fn parse(path: impl AsRef<Path>) -> Result<Config, error::Error> {
    let config_toml = std::fs::read_to_string(&path).map_err(|e| error::Kind::Io.context(e))?;

    let config = toml::from_str::<Config>(&config_toml[..])
        .map_err(|e| error::Kind::InvalidConfig.context(e))?;

    Ok(config)
}

fn app() -> Result<(), error::Error> {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/input/relayer_conf_example.toml"
    );

    let decoded = parse(path)?;
    println!("{:#?}", decoded);

    Ok(())
}

fn main() {
    if let Err(e) = app() {
        eprintln!("[error] {}", e);
        std::process::exit(1);
    };
}
