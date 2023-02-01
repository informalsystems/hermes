use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::link::{Link, LinkParameters};
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::prelude::*;

/// `relay` subcommands
#[derive(Command, Debug, Parser, Runnable)]
pub enum NewRelayCmds {
    /// Relay a single packet between two chains using the new
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

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };

        let link = match Link::new_from_opts(chains.src, chains.dst, opts, false, false) {
            Ok(link) => link,
            Err(e) => Output::error(e).exit(),
        };
    }
}
