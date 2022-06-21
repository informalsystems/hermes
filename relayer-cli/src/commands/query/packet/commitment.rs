use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::requests::{HeightQuery, IncludeProof, QueryPacketCommitmentRequest};
use serde::Serialize;
use subtle_encoding::{Encoding, Hex};

use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

#[derive(Serialize, Debug)]
struct PacketSeqs {
    height: Height,
    seqs: Vec<u64>,
}

#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct QueryPacketCommitmentCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help = "identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "port",
        required = true,
        value_name = "PORT_ID",
        help = "identifier of the port to query"
    )]
    port_id: PortId,

    #[clap(
        long = "chan",
        required = true,
        value_name = "CHANNEL_ID",
        help = "identifier of the channel to query"
    )]
    channel_id: ChannelId,

    #[clap(
        long = "seq",
        required = true,
        value_name = "SEQUENCE",
        help = "sequence of packet to query"
    )]
    sequence: Sequence,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "height of the state to query"
    )]
    height: Option<u64>,
}

impl QueryPacketCommitmentCmd {
    fn execute(&self) -> Result<String, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        let (bytes, _) = chain
            .query_packet_commitment(
                QueryPacketCommitmentRequest {
                    port_id: self.port_id.clone(),
                    channel_id: self.channel_id,
                    sequence: self.sequence,
                    height: self.height.map_or(HeightQuery::Latest, |revision_height| {
                        HeightQuery::Specific(ibc::Height::new(
                            chain.id().version(),
                            revision_height,
                        ))
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
                .unwrap_or_else(|_| format!("{:?}", bytes)))
        }
    }
}

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        match self.execute() {
            Ok(hex) => Output::success(hex).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryPacketCommitmentCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc::core::{ics24_host::identifier::{ChainId, PortId, ChannelId}, ics04_channel::packet::Sequence};

    #[test]
    fn test_query_packet_commitment_required_only() {
        assert_eq!(
            QueryPacketCommitmentCmd{ chain_id: ChainId::from_string("chain_id"), port_id: PortId::from_str("port_id").unwrap(), channel_id: ChannelId::from_str("channel-07").unwrap(), sequence: Sequence::from(42), height: None },
            QueryPacketCommitmentCmd::parse_from(&["test", "--chain", "chain_id", "--port", "port_id", "--chan", "channel-07", "--seq", "42"])
        )
    }

    #[test]
    fn test_query_packet_commitment_height() {
        assert_eq!(
            QueryPacketCommitmentCmd{ chain_id: ChainId::from_string("chain_id"), port_id: PortId::from_str("port_id").unwrap(), channel_id: ChannelId::from_str("channel-07").unwrap(), sequence: Sequence::from(42), height: Some(21) },
            QueryPacketCommitmentCmd::parse_from(&["test", "--chain", "chain_id", "--port", "port_id", "--chan", "channel-07", "--seq", "42", "--height", "21"])
        )
    }

    #[test]
    fn test_query_packet_commitment_no_seq() {
        assert!(QueryPacketCommitmentCmd::try_parse_from(&["test", "--chain", "chain_id", "--port", "port_id", "--chan", "channel-07"]).is_err())
    }

    #[test]
    fn test_query_packet_commitment_no_chan() {
        assert!(QueryPacketCommitmentCmd::try_parse_from(&["test", "--chain", "chain_id", "--port", "port_id", "--seq", "42"]).is_err())
    }

    #[test]
    fn test_query_packet_commitment_no_port() {
        assert!(QueryPacketCommitmentCmd::try_parse_from(&["test", "--chain", "chain_id", "--chan", "channel-07", "--seq", "42"]).is_err())
    }

    #[test]
    fn test_query_packet_commitment_no_chain() {
        assert!(QueryPacketCommitmentCmd::try_parse_from(&["test", "--port", "port_id", "--chan", "channel-07", "--seq", "42"]).is_err())
    }
}