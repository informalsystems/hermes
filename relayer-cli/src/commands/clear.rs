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
    counterparty_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source port")]
    port_id: PortId,

    #[clap(required = true, help = "identifier of the source channel")]
    channel_id: ChannelId,
}

impl Runnable for ClearPacketsCmd {
    fn run(&self) {
        let config = app_config();

        let chains =
            match ChainHandlePair::spawn(&config, &self.chain_id, &self.counterparty_chain_id) {
                Ok(chains) => chains,
                Err(e) => Output::error(format!("{}", e)).exit(),
            };

        let mut ev_list = vec![];

        // Construct links in both directions.
        // Some of the checks in the two Link constructor calls may be redundant;
        // going slowly, but reliably.
        let opts = LinkParameters {
            src_port_id: self.port_id.clone(),
            src_channel_id: self.channel_id.clone(),
        };
        let fwd_link =
            match Link::new_from_opts(chains.src.clone(), chains.dst.clone(), opts, false) {
                Ok(link) => link,
                Err(e) => Output::error(format!("{}", e)).exit(),
            };
        let opts = LinkParameters {
            src_port_id: fwd_link.a_to_b.dst_port_id().clone(),
            src_channel_id: fwd_link.a_to_b.dst_channel_id().clone(),
        };
        let rev_link = match Link::new_from_opts(chains.dst, chains.src, opts, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Schedule RecvPacket messages for pending packets in both directions.
        // This may produce pending acks which will be processed in the next phase.
        run_and_collect_events(&mut ev_list, || {
            fwd_link.build_and_send_recv_packet_messages()
        });
        run_and_collect_events(&mut ev_list, || {
            rev_link.build_and_send_recv_packet_messages()
        });

        // Schedule AckPacket messages in both directions.
        run_and_collect_events(&mut ev_list, || {
            fwd_link.build_and_send_ack_packet_messages()
        });
        run_and_collect_events(&mut ev_list, || {
            rev_link.build_and_send_ack_packet_messages()
        });

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
