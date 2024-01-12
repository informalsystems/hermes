use core::fmt;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use serde::Serialize;

use ibc_relayer::chain::counterparty::{
    channel_on_destination, pending_packet_summary, PendingPackets,
};
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

use crate::cli_utils::spawn_chain_counterparty;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

use super::util::CollatedPendingPackets;

/// A structure to display pending packet commitment sequence IDs
/// at both ends of a channel.
#[derive(Debug, Serialize)]
struct Summary<P> {
    /// Source chain
    src_chain: ChainId,

    /// Destination chain
    dst_chain: ChainId,

    /// The packets sent on the source chain as identified by the command.
    src: P,

    /// The packets sent on the counterparty chain.
    dst: P,
}

impl Summary<PendingPackets> {
    fn collate(self) -> Summary<CollatedPendingPackets> {
        Summary {
            src_chain: self.src_chain,
            dst_chain: self.dst_chain,

            src: CollatedPendingPackets::new(self.src),
            dst: CollatedPendingPackets::new(self.dst),
        }
    }
}

impl fmt::Display for Summary<CollatedPendingPackets> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Summary of pending packets:")?;

        writeln!(f, "Packets pending on source chain ({}):", self.src_chain)?;
        writeln!(f, "  Unreceived packets:")?;
        for seq in &self.src.unreceived_packets {
            writeln!(f, "    {}", seq)?;
        }
        writeln!(f, "  Unreceived acks:")?;
        for seq in &self.src.unreceived_acks {
            writeln!(f, "    {}", seq)?;
        }

        writeln!(
            f,
            "Packets pending on destination chain ({}):",
            self.dst_chain
        )?;
        writeln!(f, "  Unreceived packets:")?;
        for seq in &self.dst.unreceived_packets {
            writeln!(f, "    {}", seq)?;
        }
        writeln!(f, "  Unreceived acks:")?;
        for seq in &self.dst.unreceived_acks {
            writeln!(f, "    {}", seq)?;
        }

        Ok(())
    }
}

/// This command does the following:
///
/// 1. queries the chain to get its counterparty chain, channel and port identifiers (needed in 2)
/// 2. queries both chains for all packet commitments/ sequences for the given port and channel
///    and its counterparty.
/// 3. queries both chains for the unreceived sequences and acks out of the lists obtained in 2.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryPendingPacketsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain at one end of the channel"
    )]
    chain_id: ChainId,

    #[clap(
        long = "port",
        required = true,
        value_name = "PORT_ID",
        help_heading = "REQUIRED",
        help = "Port identifier on the chain given by <CHAIN_ID>"
    )]
    port_id: PortId,

    #[clap(
        long = "channel",
        visible_alias = "chan",
        required = true,
        value_name = "CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Channel identifier on the chain given by <CHAIN_ID>"
    )]
    channel_id: ChannelId,
}

impl QueryPendingPacketsCmd {
    fn execute(&self) -> Result<Summary<PendingPackets>, Error> {
        let config = app_config();

        let (chains, chan_conn_cli) = spawn_chain_counterparty::<BaseChainHandle>(
            &config,
            &self.chain_id,
            &self.port_id,
            &self.channel_id,
        )?;

        debug!(
            "fetched from source chain {} the following channel {:?}",
            self.chain_id, chan_conn_cli.channel
        );

        let src_summary = pending_packet_summary(&chains.src, &chains.dst, &chan_conn_cli.channel)
            .map_err(Error::supervisor)?;

        let counterparty_channel = channel_on_destination(
            &chan_conn_cli.channel,
            &chan_conn_cli.connection,
            &chains.dst,
        )
        .map_err(Error::supervisor)?
        .ok_or_else(|| Error::missing_counterparty_channel_id(chan_conn_cli.channel))?;

        let dst_summary = pending_packet_summary(&chains.dst, &chains.src, &counterparty_channel)
            .map_err(Error::supervisor)?;

        Ok(Summary {
            src_chain: chains.src.id(),
            dst_chain: chains.dst.id(),
            src: src_summary,
            dst: dst_summary,
        })
    }
}

impl Runnable for QueryPendingPacketsCmd {
    fn run(&self) {
        use crate::conclude::json;

        match self.execute() {
            Ok(summary) if json() => Output::success(summary).exit(),
            Ok(summary) => Output::success_msg(summary.collate().to_string()).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryPendingPacketsCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

    #[test]
    fn test_query_packet_pending() {
        assert_eq!(
            QueryPendingPacketsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap()
            },
            QueryPendingPacketsCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--channel",
                "channel-07"
            ])
        )
    }

    #[test]
    fn test_query_packet_pending_chan_alias() {
        assert_eq!(
            QueryPendingPacketsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap()
            },
            QueryPendingPacketsCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--chan",
                "channel-07"
            ])
        )
    }

    #[test]
    fn test_query_packet_pending_no_chan() {
        assert!(QueryPendingPacketsCmd::try_parse_from([
            "test", "--chain", "chain_id", "--port", "port_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_pending_no_port() {
        assert!(QueryPendingPacketsCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_pending_no_chain() {
        assert!(QueryPendingPacketsCmd::try_parse_from([
            "test",
            "--port",
            "port_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }
}
