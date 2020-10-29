use std::ops::Deref;

use crate::prelude::*;

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use relayer::config::{Config, LightClientConfig, PeersConfig};
use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint::{block::Height, net};
use tendermint_light_client::types::PeerId;

#[derive(Command, Debug, Options)]
pub struct AddCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<ChainId>,

    /// peer id for this client
    #[options(short = "i")]
    peer_id: Option<PeerId>,

    /// whether this is the primary peer
    primary: bool,

    /// trusted header hash
    #[options(short = "x")]
    hash: Option<Hash>,

    /// RPC network address
    #[options(short = "a")]
    address: Option<net::Address>,

    /// trusted header height
    #[options(short = "h")]
    height: Option<Height>,
}

#[derive(Clone, Debug)]
struct AddOptions {
    /// identifier of the chain
    chain_id: ChainId,

    /// peer id for this client
    peer_id: PeerId,

    /// RPC network address
    address: net::Address,

    /// trusted header hash
    trusted_hash: Hash,

    /// trusted header height
    trusted_height: Height,

    /// whether this is the primary peer
    primary: bool,
}

impl AddOptions {
    fn from_cmd(cmd: &AddCmd) -> Result<AddOptions, BoxError> {
        let chain_id = cmd.chain_id.clone().ok_or("missing chain identifier")?;
        let peer_id = cmd.peer_id.ok_or("missing peer identifier")?;
        let address = cmd.address.clone().ok_or("missing RPC network address")?;
        let trusted_hash = cmd.hash.ok_or("missing trusted hash")?;
        let trusted_height = cmd.height.ok_or("missing chain identifier")?;
        let primary = cmd.primary;

        Ok(AddOptions {
            chain_id,
            peer_id,
            address,
            trusted_hash,
            trusted_height,
            primary,
        })
    }
}

impl AddCmd {
    fn update_config(options: AddOptions, config: &mut Config) -> Result<PeerId, BoxError> {
        let chain_config = config
            .chains
            .iter_mut()
            .find(|c| c.id == options.chain_id)
            .ok_or_else(|| format!("could not find config for chain: {}", options.chain_id))?;

        let peers_config = chain_config.peers.get_or_insert_with(|| PeersConfig {
            primary: options.peer_id,
            peers: vec![],
        });

        let light_client_config = LightClientConfig {
            peer_id: options.peer_id,
            address: options.address.clone(),
            trusted_header_hash: options.trusted_hash,
            trusted_height: options.trusted_height,
        };

        peers_config.peers.push(light_client_config);

        if options.primary {
            peers_config.primary = options.peer_id;
        }

        Ok(peers_config.primary)
    }

    fn cmd(&self) -> Result<(), BoxError> {
        let options = AddOptions::from_cmd(self).map_err(|e| format!("invalid options: {}", e))?;
        let mut config = (*app_config()).clone();

        let new_primary = Self::update_config(options.clone(), &mut config)?;

        let config_path = crate::config::config_path()?;
        relayer::config::store(&config, config_path)?;

        status_ok!(
            "Added",
            "light client peer:\npeer_id = {}\naddress = {}\nhash = {}\nheight = {}\nprimary = {}",
            options.peer_id,
            options.address,
            options.trusted_hash,
            options.trusted_height,
            options.peer_id == new_primary,
        );

        Ok(())
    }
}

impl Runnable for AddCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}
