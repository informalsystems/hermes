use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::link::{Link, LinkParameters};

use crate::application::app_config;
use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;

/// `clear` subcommands
#[derive(Command, Debug, Parser, Runnable)]
pub enum ClearCmds {
    /// Clear outstanding packets (i.e., packet-recv and packet-ack)
    /// on a given channel in both directions.
    Packets(ClearPacketsCmd),
}

#[derive(Debug, Parser)]
pub struct ClearPacketsCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(required = true, help = "identifier of the source channel")]
    src_channel_id: ChannelId,
}

impl Runnable for ClearPacketsCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };
        let link = match Link::new_from_opts(chains.src, chains.dst, opts, false) {
            Ok(link) => link,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let mut ev = match link
            .build_and_send_recv_packet_messages()
            .map_err(Error::link)
        {
            Ok(ev) => ev,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        match link
            .build_and_send_ack_packet_messages()
            .map_err(Error::link)
        {
            Ok(mut ev1) => ev.append(&mut ev1),
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        Output::success(ev).exit()
    }
}
