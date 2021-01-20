use std::{io, io::Write, ops::Deref};

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};
use serde_json::json;
use tendermint_light_client::types::PeerId;

use ibc::ics24_host::identifier::ChainId;
use relayer::config::PeersConfig;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct RmCmd {
    /// identifiers of peers to remove
    #[options(free)]
    peer_id: Vec<PeerId>,

    /// identifier of the chain to remove peers from
    #[options(short = "c")]
    chain_id: Option<ChainId>,

    /// force removal of primary peer
    #[options(short = "f")]
    force: bool,

    /// remove all peers, implies --force
    #[options(no_short)]
    all: bool,

    /// skip confirmation
    yes: bool,
}

#[derive(Clone, Debug)]
struct RmOptions {
    /// identifier of the chain to remove peers from
    chain_id: ChainId,

    /// identifiers of peers to remove
    peer_ids: Vec<PeerId>,

    /// remove all peers, implies --force
    all: bool,

    /// force removal of primary peer
    force: bool,

    /// skip confirmation
    yes: bool,
}

impl RmOptions {
    fn from_cmd(cmd: &RmCmd) -> Result<RmOptions, BoxError> {
        let chain_id = cmd.chain_id.clone().ok_or("missing chain identifier")?;
        let peer_ids = if !cmd.all && cmd.peer_id.is_empty() {
            return Err("missing peer identifier".into());
        } else {
            cmd.peer_id.clone()
        };

        Ok(RmOptions {
            chain_id,
            peer_ids,
            all: cmd.all,
            yes: cmd.yes,
            force: cmd.force,
        })
    }
}

impl Runnable for RmCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

impl RmCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let options = RmOptions::from_cmd(self).map_err(|e| format!("invalid options: {}", e))?;
        let mut config = (*app_config()).clone();

        let chain_config = config
            .find_chain_mut(&options.chain_id)
            .ok_or_else(|| format!("could not find config for chain: {}", options.chain_id))?;

        let mut peers_config = chain_config
            .peers
            .as_mut()
            .ok_or_else(|| format!("no peers configured for chain: {}", options.chain_id))?;

        let rmd_peers = if options.all && (options.yes || confirm(&options.chain_id)?) {
            let removed_peers = get_all_peer_ids(&peers_config);
            chain_config.peers = None;

            removed_peers
        } else {
            let mut res: Vec<String> = vec![];
            for peer_id in options.peer_ids {
                let removed_peer = remove_peer(&mut peers_config, peer_id, options.force)?;
                res.push(removed_peer.to_string());
            }

            res
        };

        let config_path = crate::config::config_path()?;
        relayer::config::store(&config, config_path)?;

        Output::with_success()
            .with_result(json!(format!(
                "Removed light client peer(s) '{:?}'",
                rmd_peers
            )))
            .exit();

        Ok(())
    }
}

fn remove_peer(
    peers_config: &mut PeersConfig,
    peer_id: PeerId,
    force: bool,
) -> Result<PeerId, BoxError> {
    // Check if the given peer actually exists already, if not throw an error.
    let peer_exists = peers_config.light_client(peer_id).is_some();
    if !peer_exists {
        return Err(format!("cannot find peer: {}", peer_id).into());
    }

    // Only allow remove the primary peer if the --force option is set
    let removed_primary = peers_config.primary == peer_id;
    if removed_primary && !force {
        return Err("cannot remove primary peer, pass --force flag to force removal".into());
    }

    // Filter out the light client config with the specified peer id
    peers_config.light_clients.retain(|p| p.peer_id != peer_id);

    // If the peer we removed was the primary peer, use the next available peer as the primary,
    // if any.
    if removed_primary {
        if let Some(new_primary) = peers_config.light_clients.first() {
            peers_config.primary = new_primary.peer_id;
        }
    }

    Ok(peer_id)
}

fn get_all_peer_ids(peers_config: &PeersConfig) -> Vec<String> {
    peers_config
        .light_clients
        .iter()
        .map(|c| c.peer_id.to_string())
        .collect()
}

fn confirm(chain_id: &ChainId) -> Result<bool, BoxError> {
    loop {
        print!(
            "\n? Do you really want to remove all peers for chain '{}'? (y/n) > ",
            chain_id
        );

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
