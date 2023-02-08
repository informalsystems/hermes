// #![cfg(feature = "relayer-next")]

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer_framework::base::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_framework::base::relay::traits::two_way::HasTwoWayRelay;
use ibc_relayer_framework::base::runtime::traits::runtime::HasRuntime;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};
use tokio::runtime::Runtime as TokioRuntime;

use crate::cli_utils::{build_cosmos_birelay_context, ChainHandlePair};
use crate::conclude::Output;
use crate::prelude::*;

/// `relay` subcommands
#[derive(Command, Debug, Parser, Runnable)]
pub enum NewRelayCmds {
    /// Relay all packets between two chains using the new
    /// experimental relayer architecture.
    Packet(NewRelayPacketCmd),
}

/// Encodes the parameters of the `new-relay packet` command.
#[derive(Debug, Parser, Command)]
pub struct NewRelayPacketCmd {
    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "src-channel",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the channel associated with the source chain"
    )]
    src_channel_id: ChannelId,

    #[clap(
        long = "src-client",
        required = true,
        value_name = "SRC_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client associated with the source chain"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the port associated with the source chain"
    )]
    src_port_id: PortId,

    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "dst-channel",
        required = true,
        value_name = "DST_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the channel associated with the destination chain"
    )]
    dst_channel_id: ChannelId,

    #[clap(
        long = "dst-client",
        required = true,
        value_name = "DST_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client associated with the destination chain"
    )]
    dst_client_id: ClientId,
}

impl Runnable for NewRelayPacketCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(e).exit(),
        };

        // TODO: Read in PacketFilter policy from config
        let pf = PacketFilter::default();
        let runtime = TokioRuntime::new().unwrap();

        let relay_context = match build_cosmos_birelay_context(chains.src, chains.dst, runtime, pf)
        {
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
