use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc_relayer::link::error::LinkError;
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
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let mut ev_list = vec![];

        // Clear packets in the src -> dst direction

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };
        let link = match Link::new_from_opts(chains.src.clone(), chains.dst.clone(), opts, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        run_and_collect_events(&mut ev_list, || link.build_and_send_recv_packet_messages());
        run_and_collect_events(&mut ev_list, || link.build_and_send_ack_packet_messages());

        // Clear packets in the dst -> src direction.
        // Some of the checks in the Link constructor may be redundant;
        // going slowly, but reliably.

        let opts = LinkParameters {
            src_port_id: link.a_to_b.dst_port_id().clone(),
            src_channel_id: link.a_to_b.dst_channel_id().clone(),
        };
        let link = match Link::new_from_opts(chains.dst, chains.src, opts, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        run_and_collect_events(&mut ev_list, || link.build_and_send_recv_packet_messages());
        run_and_collect_events(&mut ev_list, || link.build_and_send_ack_packet_messages());

        Output::success(ev_list).exit()
    }
}

fn run_and_collect_events<F>(ev_list: &mut Vec<IbcEvent>, f: F)
where
    F: FnOnce() -> Result<Vec<IbcEvent>, LinkError>,
{
    match f() {
        Ok(mut ev) => ev_list.append(&mut ev),
        Err(e) => Output::error(Error::link(e)).exit(),
    };
}
