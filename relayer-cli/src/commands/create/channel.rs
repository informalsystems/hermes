use abscissa_core::{Command, Options, Runnable};

use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChainId, PortId};
use ibc_relayer::channel::Channel;
use ibc_relayer::config::StoreConfig;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::exit_with_unrecoverable_error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateChannelCommand {
    #[options(
        free,
        required,
        help = "Identifier of the side `a` chain for the new channel"
    )]
    chain_a_id: ChainId,

    #[options(free, help = "Identifier of the side `b` chain for the new channel")]
    chain_b_id: Option<ChainId>,

    #[options(help = "Identifier of the side `a` port for the new channel")]
    port_a: PortId,

    #[options(help = "Identifier of the side `b` port for the new channel")]
    port_b: PortId,

    #[options(help = "The order for parametrizing the new channel")]
    order: Order,

    #[options(help = "The version for parametrizing the new channel")]
    version: String,
}

impl Runnable for CreateChannelCommand {
    fn run(&self) {
        match &self.chain_b_id {
            None => unimplemented!(),
            Some(chain_b) => self.run_using_new_connection(chain_b),
        }
    }
}

impl CreateChannelCommand {
    // Creates a new channel, as well as a new underlying connection and clients.
    fn run_using_new_connection(&self, chain_b_id: &ChainId) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

        let chains =
            ChainHandlePair::spawn_with(spawn_options, &config, &self.chain_a_id, chain_b_id)
                .unwrap_or_else(exit_with_unrecoverable_error);
        info!(
            "Creating new clients, new connection, and a new channel with order {:?} and version {}",
            self.order, self.version
        );

        let client_a = ForeignClient::new(chains.src.clone(), chains.dst.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);
        let client_b = ForeignClient::new(chains.dst.clone(), chains.src.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Create the connection.
        // TODO: pass the `delay` parameter here.
        let con =
            Connection::new(client_a, client_b, 0).unwrap_or_else(exit_with_unrecoverable_error);

        // Finally create the channel.
        let chan_res = Channel::new(con, self.order, self.port_a.clone(), self.port_b.clone());
    }
}
