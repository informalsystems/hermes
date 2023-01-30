use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::counterparty::commitments_on_chain;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

use super::util::PacketSeqs;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryPacketCommitmentsCmd {
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

impl QueryPacketCommitmentsCmd {
    fn execute(&self) -> Result<PacketSeqs, Error> {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        commitments_on_chain(&chain, &self.port_id, &self.channel_id)
            .map_err(Error::supervisor)
            .map(|(seqs_vec, height)| PacketSeqs {
                height,
                seqs: seqs_vec,
            })
    }
}

// cargo run --bin hermes -- query packet commitments --chain ibc-0 --port transfer --channel ibconexfer --height 3
impl Runnable for QueryPacketCommitmentsCmd {
    fn run(&self) {
        use crate::conclude::json;

        match self.execute() {
            Ok(p) if json() => Output::success(p).exit(),
            Ok(p) => Output::success(p.collated()).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryPacketCommitmentsCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

    #[test]
    fn test_query_packet_commitments() {
        assert_eq!(
            QueryPacketCommitmentsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap()
            },
            QueryPacketCommitmentsCmd::parse_from([
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
    fn test_query_packet_commitments_chan_alias() {
        assert_eq!(
            QueryPacketCommitmentsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap()
            },
            QueryPacketCommitmentsCmd::parse_from([
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
    fn test_query_packet_commitments_no_chan() {
        assert!(QueryPacketCommitmentsCmd::try_parse_from([
            "test", "--chain", "chain_id", "--port", "port_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_commitments_no_port() {
        assert!(QueryPacketCommitmentsCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_commitments_no_chain() {
        assert!(QueryPacketCommitmentsCmd::try_parse_from([
            "test",
            "--port",
            "port_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }
}
