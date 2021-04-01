use std::{fmt, io, io::Write, ops::Deref, path::PathBuf};

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use config::StoreConfig;
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config,
    config::{Config, LightClientConfig, PeersConfig},
    util::block_on,
};
use tendermint::block::Height;
use tendermint::hash::Hash;
use tendermint_light_client::types::PeerId;
use tendermint_rpc::{Client, HttpClient};

use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct AddCmd {
    /// RPC network address (required)
    #[options(free)]
    address: Option<tendermint_rpc::Url>,

    /// identifier of the chain (required)
    #[options(short = "c")]
    chain_id: Option<ChainId>,

    /// path to light client store for this peer (required)
    store: Option<PathBuf>,

    /// whether this is the primary peer
    primary: bool,

    /// allow overriding an existing peer
    force: bool,

    /// skip confirmation
    yes: bool,

    /// override peer id (optional)
    #[options(no_short)]
    peer_id: Option<PeerId>,

    /// override height (optional)
    #[options(no_short)]
    height: Option<Height>,

    /// override hash (optional)
    #[options(no_short)]
    hash: Option<Hash>,
}

impl AddCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = (*app_config()).clone();
        let options = AddOptions::from_cmd(self).map_err(|e| format!("invalid options: {}", e))?;

        options
            .validate()
            .map_err(|e| format!("invalid options: {}", e))?;

        add(config, options)
    }
}

impl Runnable for AddCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

#[derive(Clone, Debug)]
struct AddOptions {
    /// identifier of the chain
    chain_id: ChainId,

    /// RPC network address
    address: tendermint_rpc::Url,

    /// whether this is the primary peer or not
    primary: bool,

    /// path to light client store for this peer
    store: PathBuf,

    /// override peer id
    override_peer_id: Option<PeerId>,

    /// override height
    override_height: Option<Height>,

    /// override hash
    override_hash: Option<Hash>,

    /// allow overriding an existing peer
    force: bool,

    /// skip confirmation
    yes: bool,
}

impl AddOptions {
    fn from_cmd(cmd: &AddCmd) -> Result<AddOptions, BoxError> {
        let chain_id = cmd.chain_id.clone().ok_or("missing chain identifier")?;
        let address = cmd.address.clone().ok_or("missing RPC network address")?;
        let store_path = cmd.store.clone().ok_or("missing store path")?;

        Ok(AddOptions {
            chain_id,
            address,
            store: store_path,
            override_peer_id: cmd.peer_id,
            override_height: cmd.height,
            override_hash: cmd.hash,
            primary: cmd.primary,
            force: cmd.force,
            yes: cmd.yes,
        })
    }

    fn validate(&self) -> Result<(), BoxError> {
        if !self.store.exists() {
            return Err(format!("Store path '{}' does not exists", self.store.display()).into());
        }

        if !self.store.is_dir() {
            return Err(format!("Store path '{}' is not a directory", self.store.display()).into());
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct NodeStatus {
    chain_id: ChainId,
    address: tendermint_rpc::Url,
    peer_id: PeerId,
    hash: Hash,
    height: Height,
}

impl fmt::Display for NodeStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  chain id: {}", self.chain_id)?;
        writeln!(f, "  address:  {}", self.address)?;
        writeln!(f, "  peer id:  {}", self.peer_id)?;
        writeln!(f, "  height:   {}", self.height)?;
        writeln!(f, "  hash:     {}", self.hash)?;

        Ok(())
    }
}

fn add(mut config: Config, options: AddOptions) -> Result<(), BoxError> {
    // Fetch the status from the node
    let mut status = fetch_status(options.chain_id.clone(), options.address.clone())?;

    // Override the fetched status with command line arguments, if given
    override_status(&mut status, &options);

    // Ask the user for confirmation if --yes was not supplied
    if !(options.yes || confirm(&status, options.primary)?) {
        return Ok(());
    }

    // Update the in-memory configuration
    let new_primary = update_config(options, status.clone(), &mut config)?;

    // Write the updated configuration to disk
    let config_path = crate::config::config_path()?;
    ibc_relayer::config::store(&config, config_path)?;

    status_ok!(
        "Success",
        "Added light client:\n{}  primary:  {}",
        status,
        status.peer_id == new_primary,
    );

    Ok(())
}

fn fetch_status(chain_id: ChainId, address: tendermint_rpc::Url) -> Result<NodeStatus, BoxError> {
    let rpc_client = HttpClient::new(address.clone())?;
    let response = block_on(rpc_client.status())?;

    let peer_id = response.node_info.id;
    let height = response.sync_info.latest_block_height;
    let hash = response.sync_info.latest_block_hash;

    Ok(NodeStatus {
        chain_id,
        address,
        peer_id,
        hash,
        height,
    })
}

fn override_status(status: &mut NodeStatus, options: &AddOptions) {
    if let Some(peer_id) = options.override_peer_id {
        status.peer_id = peer_id;
    }

    if let Some(height) = options.override_height {
        status.height = height;
    }

    if let Some(hash) = options.override_hash {
        status.hash = hash;
    }
}

fn confirm(status: &NodeStatus, primary: bool) -> Result<bool, BoxError> {
    print!("Light client configuration:\n{}", status);
    println!("  primary:  {}", primary);

    loop {
        print!("\n? Do you want to add a new light client with these trust options? (y/n) > ");
        io::stdout().flush()?; // need to flush stdout since stdout is often line-buffered

        let mut choice = String::new();
        io::stdin().read_line(&mut choice)?;

        match choice.trim_end() {
            "y" | "yes" => return Ok(true),
            "n" | "no" => return Ok(false),
            _ => continue,
        }
    }
}

fn update_config(
    options: AddOptions,
    status: NodeStatus,
    config: &mut Config,
) -> Result<PeerId, BoxError> {
    let chain_config = config
        .find_chain_mut(&options.chain_id)
        .ok_or_else(|| format!("could not find config for chain: {}", options.chain_id))?;

    let peers_config = chain_config.peers.get_or_insert_with(|| PeersConfig {
        primary: status.peer_id,
        light_clients: vec![],
    });

    // Check if the given peer exists already, in which case throw an error except if the
    // --force flag is set.
    let peer_exists = peers_config.light_client(status.peer_id).is_some();
    if peer_exists && !options.force {
        return Err(format!(
            "a peer with id {} already exists, remove it first \
            or pass the --force flag to override it",
            status.peer_id
        )
        .into());
    }

    let light_client_config = LightClientConfig {
        peer_id: status.peer_id,
        address: status.address.clone(),
        timeout: config::default::timeout(),
        trusted_header_hash: status.hash,
        trusted_height: status.height,
        store: StoreConfig::Disk {
            path: options.store.join(status.peer_id.to_string()),
        },
    };

    if peer_exists {
        // Filter out the light client config with the specified peer id
        peers_config
            .light_clients
            .retain(|p| p.peer_id != status.peer_id);
    }

    peers_config.light_clients.push(light_client_config);

    if options.primary {
        peers_config.primary = status.peer_id;
    }

    Ok(peers_config.primary)
}
