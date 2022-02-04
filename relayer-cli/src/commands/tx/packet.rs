use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc_relayer::link::{Link, LinkParameters};

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawPacketRecvCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(required = true, help = "identifier of the source channel")]
    src_channel_id: ChannelId,
}

impl Runnable for TxRawPacketRecvCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };
        let link = match Link::new_from_opts(chains.src, chains.dst, opts, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> = link
            .build_and_send_recv_packet_messages()
            .map_err(Error::link);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawPacketAckCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(required = true, help = "identifier of the source channel")]
    src_channel_id: ChannelId,
}

impl Runnable for TxRawPacketAckCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };
        let link = match Link::new_from_opts(chains.src, chains.dst, opts, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> = link
            .build_and_send_ack_packet_messages()
            .map_err(Error::link);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
