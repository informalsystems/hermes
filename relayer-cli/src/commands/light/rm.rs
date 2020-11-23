use std::ops::Deref;

use crate::prelude::*;

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use relayer::config::Config;
use tendermint_light_client::types::PeerId;

#[derive(Command, Debug, Options)]
pub struct RmCmd {
    /// peer id for this client
    #[options(free)]
    peer_id: Option<PeerId>,

    #[options(short = "c")]
    /// identifier of the chain
    chain_id: Option<ChainId>,

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
            .iter_mut()
            .find(|c| c.id == options.chain_id)
            .ok_or_else(|| format!("could not find config for chain: {}", options.chain_id))?;

        let peers_config = chain_config
            .peers
            .as_mut()
            .ok_or_else(|| format!("no peers configured for chain: {}", options.chain_id))?;

        // Check if the given peer actually exists already, if not throw an error.
        let peer_exists = peers_config.light_client(options.peer_id).is_some();
        if !peer_exists {
            return Err(format!("cannot find peer: {}", options.peer_id).into());
        }

        // Only allow remove the primary peer if the --force option is set
        let is_primary = peers_config.primary == options.peer_id;
        if is_primary && !options.force {
            return Err("cannot remove primary peer, pass --force flag to force removal".into());
        }

        // Filter out the light client config with the specified peer id
        peers_config
            .light_clients
            .retain(|p| p.peer_id != options.peer_id);

        // Disallow removing the last remaining peer
        if peers_config.light_clients.is_empty() {
            return Err(
                "cannot remove last remaining peer, add other peers before removing this one"
                    .into(),
            );
        }

        // If the peer we removed was the primary peer, use the next available peer as the primary
        if is_primary {
            let new_primary = peers_config.light_clients.first().unwrap(); // SAFETY: safe because of check above
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
