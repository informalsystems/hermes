use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use serde::Serialize;

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::chain::counterparty::{
    channel_on_destination, pending_packet_summary, PendingPackets,
};
use ibc_relayer::chain::handle::BaseChainHandle;

use crate::cli_utils::spawn_chain_counterparty;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

/// A structure to display pending packet commitment sequence IDs
/// at both ends of a channel.
#[derive(Debug, Serialize)]
struct Summary {
    /// The packets sent on the identified chain.
    forward: PendingPackets,
    /// The packets sent on the counterparty chain.
    reverse: PendingPackets,
}

/// This command does the following:
///
/// 1. queries the chain to get its counterparty chain, channel and port identifiers (needed in 2)
/// 2. queries both chains for all packet commitments/ sequences for the given port and channel
///    and its counterparty.
/// 3. queries both chains for the unreceived sequences and acks out of the lists obtained in 2.
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryPendingPacketsCmd {
    #[clap(
        required = true,
        help = "identifier of the chain at one end of the channel"
    )]
    chain_id: ChainId,

    #[clap(
        required = true,
        help = "port identifier on the chain given by <CHAIN_ID>"
    )]
    port_id: PortId,

    #[clap(
        required = true,
        help = "channel identifier on the chain given by <CHAIN_ID>"
    )]
    channel_id: ChannelId,
}

impl QueryPendingPacketsCmd {
    fn execute(&self) -> Result<Summary, Error> {
        let config = app_config();

        let (chains, ccc) = spawn_chain_counterparty::<BaseChainHandle>(
            &config,
            &self.chain_id,
            &self.port_id,
            &self.channel_id,
        )?;

        debug!(
            chain=%self.chain_id,
            "fetched channel from source chain: {:?}",
            ccc.channel
        );

        let forward = pending_packet_summary(&chains.src, &chains.dst, &ccc.channel)
            .map_err(Error::supervisor)?;
        let counterparty_channel =
            channel_on_destination(&ccc.channel, &ccc.connection, &chains.dst)
                .map_err(Error::supervisor)?
                .ok_or_else(|| Error::missing_counterparty_channel_id(ccc.channel))?;
        let reverse = pending_packet_summary(&chains.dst, &chains.src, &counterparty_channel)
            .map_err(Error::supervisor)?;
        Ok(Summary { forward, reverse })
    }
}

impl Runnable for QueryPendingPacketsCmd {
    fn run(&self) {
        match self.execute() {
            Ok(pending) => Output::success(pending).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
