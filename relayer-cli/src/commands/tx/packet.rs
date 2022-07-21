use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc_relayer::link::{Link, LinkParameters};

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct TxPacketRecvCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel"
    )]
    src_channel_id: ChannelId,
}

impl Runnable for TxPacketRecvCmd {
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
        let link = match Link::new_from_opts(chains.src, chains.dst, opts, false, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> = link
            .relay_recv_packet_and_timeout_messages()
            .map_err(Error::link);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct TxPacketAckCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel"
    )]
    src_channel_id: ChannelId,
}

impl Runnable for TxPacketAckCmd {
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
        let link = match Link::new_from_opts(chains.src, chains.dst, opts, false, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> =
            link.relay_ack_packet_messages().map_err(Error::link);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{TxPacketAckCmd, TxPacketRecvCmd};

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

    #[test]
    fn test_packet_recv() {
        assert_eq!(
            TxPacketRecvCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_port_id: PortId::from_str("port_sender").unwrap(),
                src_channel_id: ChannelId::from_str("channel_sender").unwrap()
            },
            TxPacketRecvCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-port",
                "port_sender",
                "--src-channel",
                "channel_sender"
            ])
        )
    }

    #[test]
    fn test_packet_recv_aliases() {
        assert_eq!(
            TxPacketRecvCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_port_id: PortId::from_str("port_sender").unwrap(),
                src_channel_id: ChannelId::from_str("channel_sender").unwrap()
            },
            TxPacketRecvCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-port",
                "port_sender",
                "--src-chan",
                "channel_sender"
            ])
        )
    }

    #[test]
    fn test_packet_recv_no_sender_channel() {
        assert!(TxPacketRecvCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--src-port",
            "port_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_recv_no_sender_port() {
        assert!(TxPacketRecvCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--src-channel",
            "channel_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_recv_no_sender_chain() {
        assert!(TxPacketRecvCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-port",
            "port_sender",
            "--src-channel",
            "channel_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_recv_no_receiver_chain() {
        assert!(TxPacketRecvCmd::try_parse_from(&[
            "test",
            "--src-chain",
            "chain_sender",
            "--src-port",
            "port_sender",
            "--src-channel",
            "channel_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_ack() {
        assert_eq!(
            TxPacketAckCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_port_id: PortId::from_str("port_sender").unwrap(),
                src_channel_id: ChannelId::from_str("channel_sender").unwrap()
            },
            TxPacketAckCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-port",
                "port_sender",
                "--src-channel",
                "channel_sender"
            ])
        )
    }

    #[test]
    fn test_packet_ack_aliases() {
        assert_eq!(
            TxPacketAckCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_port_id: PortId::from_str("port_sender").unwrap(),
                src_channel_id: ChannelId::from_str("channel_sender").unwrap()
            },
            TxPacketAckCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-port",
                "port_sender",
                "--src-chan",
                "channel_sender"
            ])
        )
    }

    #[test]
    fn test_packet_ack_no_sender_channel() {
        assert!(TxPacketAckCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--src-port",
            "port_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_ack_no_sender_port() {
        assert!(TxPacketAckCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--src-channel",
            "channel_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_ack_no_sender_chain() {
        assert!(TxPacketAckCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-port",
            "port_sender",
            "--src-channel",
            "channel_sender"
        ])
        .is_err())
    }

    #[test]
    fn test_packet_ack_no_receiver_chain() {
        assert!(TxPacketAckCmd::try_parse_from(&[
            "test",
            "--src-chain",
            "chain_sender",
            "--src-port",
            "port_sender",
            "--src-channel",
            "channel_sender"
        ])
        .is_err())
    }
}
