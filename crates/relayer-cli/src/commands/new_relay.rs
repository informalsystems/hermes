// #![cfg(feature = "relayer-next")]

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_framework::base::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_framework::base::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_framework::base::runtime::traits::runtime::HasRuntime;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use tokio::runtime::Runtime as TokioRuntime;

use crate::cli_utils::{build_cosmos_birelay_context, ChainHandlePair};
use crate::conclude::Output;
use crate::prelude::*;

/// `relay` subcommands which utilize the experimental relayer architecture.
#[derive(Command, Debug, Parser, Runnable)]
pub enum NewRelayCmds {
    /// Relay all packets between two chains using the experimental
    /// relayer architecture.
    Packets(NewRelayPacketsCmd),
}

/// Encodes the parameters of the experimental `relay packet` command
/// which utilizes the experiemental relayer architecture.
#[derive(Debug, Parser, Command)]
pub struct NewRelayPacketsCmd {
    #[clap(
        long = "chain-a",
        required = true,
        value_name = "CHAIN_A_ID",
        help_heading = "REQUIRED",
        help = "Identifier of chain A"
    )]
    chain_a_id: ChainId,

    #[clap(
        long = "client-a",
        required = true,
        value_name = "CLIENT_A_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client associated with chain A"
    )]
    client_a_id: ClientId,

    #[clap(
        long = "chain-b",
        required = true,
        value_name = "CHAIN_B_ID",
        help_heading = "REQUIRED",
        help = "Identifier of chain B"
    )]
    chain_b_id: ChainId,

    #[clap(
        long = "client-b",
        required = true,
        value_name = "CLIENT_B_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client associated with chain B"
    )]
    client_b_id: ClientId,
}

impl Runnable for NewRelayPacketsCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.chain_a_id, &self.chain_b_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(e).exit(),
        };

        // TODO: Read in PacketFilter policy from config
        let pf = PacketFilter::default();
        let runtime = TokioRuntime::new().unwrap();

        let relay_context = match build_cosmos_birelay_context(
            chains.src,
            chains.dst,
            self.client_a_id.clone(),
            self.client_b_id.clone(),
            runtime,
            pf,
        ) {
            Ok(rc) => rc,
            Err(e) => Output::error(e).exit(),
        };

        relay_context
            .relay_a_to_b()
            .runtime()
            .runtime
            .runtime
            .block_on(relay_context.auto_relay());
    }
}
