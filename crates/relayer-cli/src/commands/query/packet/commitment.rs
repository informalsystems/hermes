use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::requests::{IncludeProof, QueryHeight, QueryPacketCommitmentRequest};
use serde::Serialize;
use subtle_encoding::{Encoding, Hex};

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer_types::Height;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;

#[derive(Serialize, Debug)]
struct PacketSeqs {
    height: Height,
    seqs: Vec<u64>,
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryPacketCommitmentCmd {
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

    #[clap(
        long = "sequence",
        visible_alias = "seq",
        required = true,
        value_name = "SEQUENCE",
        help_heading = "REQUIRED",
        help = "Sequence of packet to query"
    )]
    sequence: Sequence,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "Height of the state to query. Leave unspecified for latest height."
    )]
    height: Option<u64>,
}

impl QueryPacketCommitmentCmd {
    fn execute(&self) -> Result<String, Error> {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        let (bytes, _) = chain
            .query_packet_commitment(
                QueryPacketCommitmentRequest {
                    port_id: self.port_id.clone(),
                    channel_id: self.channel_id.clone(),
                    sequence: self.sequence,
                    height: self.height.map_or(QueryHeight::Latest, |revision_height| {
                        QueryHeight::Specific(
                            Height::new(chain.id().version(), revision_height)
                                .unwrap_or_else(exit_with_unrecoverable_error),
                        )
                    }),
                },
                IncludeProof::No,
            )
            .map_err(Error::relayer)?;

        if bytes.is_empty() {
            Ok("None".to_owned())
        } else {
            Ok(Hex::upper_case()
                .encode_to_string(bytes.clone())
                .unwrap_or_else(|_| format!("{bytes:?}")))
        }
    }
}

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        match self.execute() {
            Ok(hex) => Output::success(hex).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryPacketCommitmentCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::{
        ics04_channel::packet::Sequence,
        ics24_host::identifier::{ChainId, ChannelId, PortId},
    };

    #[test]
    fn test_query_packet_commitment_required_only() {
        assert_eq!(
            QueryPacketCommitmentCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                sequence: Sequence::from(42),
                height: None
            },
            QueryPacketCommitmentCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--channel",
                "channel-07",
                "--sequence",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_packet_commitment_aliases() {
        assert_eq!(
            QueryPacketCommitmentCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                sequence: Sequence::from(42),
                height: None
            },
            QueryPacketCommitmentCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--chan",
                "channel-07",
                "--seq",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_packet_commitment_height() {
        assert_eq!(
            QueryPacketCommitmentCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                sequence: Sequence::from(42),
                height: Some(21)
            },
            QueryPacketCommitmentCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--channel",
                "channel-07",
                "--sequence",
                "42",
                "--height",
                "21"
            ])
        )
    }

    #[test]
    fn test_query_packet_commitment_no_seq() {
        assert!(QueryPacketCommitmentCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--port",
            "port_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_commitment_no_chan() {
        assert!(QueryPacketCommitmentCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--port",
            "port_id",
            "--sequence",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_commitment_no_port() {
        assert!(QueryPacketCommitmentCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--channel",
            "channel-07",
            "--sequence",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_query_packet_commitment_no_chain() {
        assert!(QueryPacketCommitmentCmd::try_parse_from([
            "test",
            "--port",
            "port_id",
            "--channel",
            "channel-07",
            "--sequence",
            "42"
        ])
        .is_err())
    }
}
