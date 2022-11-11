use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::counterparty::acknowledgements_on_chain;
use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

use crate::cli_utils::spawn_chain_counterparty;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

use super::util::PacketSeqs;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryPacketAcknowledgementsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "port",
        required = true,
        value_name = "PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the port to query"
    )]
    port_id: PortId,

    #[clap(
        long = "channel",
        visible_alias = "chan",
        required = true,
        value_name = "CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the channel to query"
    )]
    channel_id: ChannelId,
}

impl QueryPacketAcknowledgementsCmd {
    fn execute(&self) -> Result<PacketSeqs, Error> {
        let config = app_config();

        let (chains, chan_conn_cli) = spawn_chain_counterparty::<BaseChainHandle>(
            &config,
            &self.chain_id,
            &self.port_id,
            &self.channel_id,
        )?;

        let (seqs, height) =
            acknowledgements_on_chain(&chains.src, &chains.dst, &chan_conn_cli.channel)
                .map_err(Error::supervisor)?;

        Ok(PacketSeqs { seqs, height })
    }
}

// cargo run --bin hermes -- query packet acknowledgements --chain ibc-0 --port transfer --connection ibconexfer --height 3
impl Runnable for QueryPacketAcknowledgementsCmd {
    fn run(&self) {
        use crate::conclude::json;

        match self.execute() {
            Ok(p) if json() => Output::success(p).exit(),
            Ok(p) => Output::success(p.collated()).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryPacketAcknowledgementsCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

    #[test]
    fn test_query_packet_acks() {
        assert_eq!(
            QueryPacketAcknowledgementsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap()
            },
            QueryPacketAcknowledgementsCmd::parse_from([
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
    fn test_query_packet_acks_chan_alias() {
        assert_eq!(
            QueryPacketAcknowledgementsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap()
            },
            QueryPacketAcknowledgementsCmd::parse_from([
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
    fn test_query_packet_acks_no_chan() {
        assert!(QueryPacketAcknowledgementsCmd::try_parse_from([
            "test", "--chain", "chain_id", "--port", "port_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_acks_no_port() {
        assert!(QueryPacketAcknowledgementsCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_acks_no_chain() {
        assert!(QueryPacketAcknowledgementsCmd::try_parse_from([
            "test",
            "--port",
            "port_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }
}
