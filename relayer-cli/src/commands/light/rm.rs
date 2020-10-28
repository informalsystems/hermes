use std::ops::Deref;

use crate::prelude::*;

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use relayer::config::Config;
use tendermint::chain::Id as ChainId;
use tendermint_light_client::types::PeerId;

#[derive(Command, Debug, Options)]
pub struct RmCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<ChainId>,

    /// peer id for this client
    #[options(short = "i")]
    peer_id: Option<PeerId>,

    /// force removal of primary peer
    #[options(short = "f")]
    force: bool,
}

#[derive(Clone, Debug)]
struct RmOptions {
    /// identifier of the chain
    chain_id: ChainId,

    /// peer id for this client
    peer_id: PeerId,

    /// force removal of primary peer
    force: bool,
}

impl RmOptions {
    fn from_cmd(cmd: &RmCmd) -> Result<RmOptions, BoxError> {
        let chain_id = cmd.chain_id.clone().ok_or("missing chain identifier")?;
        let peer_id = cmd.peer_id.ok_or("missing peer identifier")?;
        let force = cmd.force;

        Ok(RmOptions {
            chain_id,
            peer_id,
            force,
        })
    }
}

impl RmCmd {
    fn update_config(options: RmOptions, config: &mut Config) -> Result<PeerId, BoxError> {
        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == options.chain_id)
            .ok_or_else(|| format!("could not find config for chain: {}", options.chain_id))?;

        let peers_config = config
            .light_clients
            .get_mut(&chain_config.id)
            .ok_or_else(|| format!("no peers configured for chain: {}", options.chain_id))?;

        let peer_exists = !peers_config
            .peers
            .iter()
            .any(|p| p.peer_id == options.peer_id);

        if !peer_exists {
            return Err(format!("cannot find peer: {}", options.peer_id).into());
        }

        let is_primary = peers_config.primary == options.peer_id;
        if is_primary && !options.force {
            return Err("cannot remove primary peer, pass --force flag to force removal".into());
        }

        peers_config.peers.retain(|p| p.peer_id != options.peer_id);

        if peers_config.peers.is_empty() {
            return Err("cannot remove sole peer, add other peers before removing this one".into());
        }

        if is_primary {
            let new_primary = peers_config.peers.first().unwrap(); // SAFETY: safe because of emptiness check above
            peers_config.primary = new_primary.peer_id;
        }

        Ok(options.peer_id)
    }

    fn cmd(&self) -> Result<(), BoxError> {
        let options = RmOptions::from_cmd(self).map_err(|e| format!("invalid options: {}", e))?;
        let mut config = (*app_config()).clone();

        let removed_peer = Self::update_config(options, &mut config)?;

        let config_path = crate::config::config_path()?;
        relayer::config::store(&config, config_path)?;

        status_ok!("Removed", "light client peer '{}'", removed_peer);

        Ok(())
    }
}

impl Runnable for RmCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}
