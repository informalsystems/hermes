//! `channel` subcommand
use abscissa_core::{Command, Help, Options, Runnable};

use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChainId, PortId};
use ibc_relayer::config::{RelayPath, StoreConfig};
use ibc_relayer::relay::connect_with_new_channel;

use crate::application::app_config;
use crate::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::Output;

/// `channel` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum ChannelCmds {
    /// The `help` subcommand
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// The `tx raw` subcommand
    #[options(help = "tx raw")]
    Handshake(ChannelHandshakeCommand),
}

#[derive(Clone, Command, Debug, Options)]
pub struct ChannelHandshakeCommand {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(help = "the channel order", short = "o")]
    ordering: Order,
}

impl Runnable for ChannelHandshakeCommand {
    fn run(&self) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());
        let chains = match ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &self.src_chain_id,
            &self.dst_chain_id,
        ) {
            Ok(chains) => chains,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let res = connect_with_new_channel(
            chains.src,
            chains.dst,
            self.ordering,
            RelayPath {
                a_port: self.src_port_id.clone(),
                b_port: self.dst_port_id.clone(),
            },
        );

        match res {
            Ok(channel) => Output::success(channel).exit(),
            Err(e) => Output::error(format!("{:?}", e)).exit(),
        }
    }
}
