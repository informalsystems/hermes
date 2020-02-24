#![deny(warnings)]

/// Read the relayer configuration into the Config struct, in examples for now
/// to support ADR validation..should move to relayer/src soon
use {serde_derive::Deserialize, std::fs::File, std::io::Read, std::path::PathBuf};

#[derive(Debug, Deserialize)]
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
/// TODO: If a file cannot be found, return a default Config allowing relayer
/// to relay everything from any to any chain(?)
/// If we find a file but cannot parse it, panic
fn parse(path: String) -> Config {
    let mut file = File::open(&path).expect("Unable to open");
    let mut config_toml = String::new();

    file.read_to_string(&mut config_toml)
        .unwrap_or_else(|err| panic!("Error while reading config: [{}]", err));
    toml::from_str(&config_toml[..]).unwrap()
}

fn main() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("examples/input/relayer_conf_example.toml");
    let my_str = d.into_os_string().into_string().unwrap();
    let decoded = parse(my_str);
    println!("{:#?}", decoded);
}
