use std::{fmt, io, io::Write, ops::Deref};

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use relayer::{
    config::{Config, LightClientConfig, PeersConfig},
    util::block_on,
};
use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint::{block::Height, net};
use tendermint_light_client::types::PeerId;
use tendermint_rpc::{Client, HttpClient};

use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct AddCmd {
    /// RPC network address
    #[options(free)]
    address: Option<net::Address>,

    /// identifier of the chain
    #[options(short = "c")]
    chain_id: Option<ChainId>,

    /// whether this is the primary peer
    primary: bool,

    /// allow overriding an existing peer
    force: bool,

    /// skip confirmation
    yes: bool,
}

#[derive(Clone, Debug)]
struct AddOptions {
    /// identifier of the chain
    chain_id: ChainId,

    /// RPC network address
    address: net::Address,

    /// whether this is the primary peer or not
    primary: bool,

    /// allow overriding an existing peer
    force: bool,

    /// skip confirmation
    yes: bool,
}

impl AddOptions {
    fn from_cmd(cmd: &AddCmd) -> Result<AddOptions, BoxError> {
        let chain_id = cmd.chain_id.clone().ok_or("missing chain identifier")?;
        let address = cmd.address.clone().ok_or("missing RPC network address")?;
        let primary = cmd.primary;
        let force = cmd.force;
        let yes = cmd.yes;

        Ok(AddOptions {
            chain_id,
            address,
            primary,
            force,
            yes,
        })
    }
}

#[derive(Debug, Clone)]
pub struct NodeStatus {
    chain_id: ChainId,
    address: net::Address,
    peer_id: PeerId,
    latest_hash: Hash,
    latest_height: Height,
}

impl fmt::Display for NodeStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  chain id: {}", self.chain_id)?;
        writeln!(f, "  address:  {}", self.address)?;
        writeln!(f, "  peer id:  {}", self.peer_id)?;
        writeln!(f, "  height:   {}", self.latest_height)?;
        writeln!(f, "  hash:     {}", self.latest_hash)?;

        Ok(())
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

fn add(mut config: Config, options: AddOptions) -> Result<(), BoxError> {
    let status = fetch_status(options.chain_id.clone(), options.address.clone())?;

    if !(options.yes || confirm(&status, options.primary)?) {
        return Ok(());
    }

    let new_primary = update_config(options, status.clone(), &mut config)?;

    let config_path = crate::config::config_path()?;
    relayer::config::store(&config, config_path)?;

    status_ok!(
        "Success",
        "Added light client:\n{}  primary:  {}",
        status,
        status.peer_id == new_primary,
    );

    Ok(())
}

fn fetch_status(chain_id: ChainId, address: net::Address) -> Result<NodeStatus, BoxError> {
    let rpc_client = HttpClient::new(address.clone())?;
    let response = block_on(rpc_client.status())?;

    let peer_id = response.node_info.id;
    let latest_height = response.sync_info.latest_block_height;
    let latest_hash = response.sync_info.latest_block_hash;

    Ok(NodeStatus {
        chain_id,
        address,
        peer_id,
        latest_hash,
        latest_height,
    })
}

fn update_config(
    options: AddOptions,
    status: NodeStatus,
    config: &mut Config,
) -> Result<PeerId, BoxError> {
    let chain_config = config
        .chains
        .iter_mut()
        .find(|c| c.id == options.chain_id)
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
        trusted_header_hash: status.latest_hash,
        trusted_height: status.latest_height,
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

impl AddCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = (*app_config()).clone();
        let options = AddOptions::from_cmd(self).map_err(|e| format!("invalid options: {}", e))?;

        add(config, options)
    }
}

impl Runnable for AddCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}
