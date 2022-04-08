use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::events::IbcEvent;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::{Channel, ChannelSide};

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

macro_rules! tx_chan_cmd {
    ($dbg_string:literal, $func:ident, $self:expr, $chan:expr) => {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &$self.src_chain_id, &$self.dst_chain_id)
        {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains
            .dst
            .query_connection(&$self.dst_conn_id, Height::default())
        {
            Ok(connection) => connection,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let channel = $chan(chains, dst_connection);

        info!("Message {}: {:?}", $dbg_string, channel);

        let res: Result<IbcEvent, Error> = channel.$func().map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    };
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawChanOpenInitCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[clap(required = true, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(
        short,
        long,
        default_value_t,
        help = "the channel ordering, valid options 'unordered' (default) and 'ordered'"
    )]
    order: Order,
}

impl Runnable for TxRawChanOpenInitCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains
            .dst
            .query_connection(&self.dst_conn_id, Height::default())
        {
            Ok(connection) => connection,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let channel = Channel {
            connection_delay: Default::default(),
            ordering: self.order,
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                self.src_port_id.clone(),
                None,
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                dst_connection.client_id().clone(),
                self.dst_conn_id.clone(),
                self.dst_port_id.clone(),
                None,
                None,
            ),
        };

        info!("Message ChanOpenInit: {:?}", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_open_init_and_send()
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawChanOpenTryCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[clap(required = true, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(
        short = 's',
        long,
        required = true,
        help = "identifier of the source channel (required)",
        value_name = "ID"
    )]
    src_chan_id: ChannelId,

    #[clap(
        short = 'd',
        long,
        help = "identifier of the destination channel (optional)",
        value_name = "ID"
    )]
    dst_chan_id: Option<ChannelId>,
}

impl Runnable for TxRawChanOpenTryCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenTry",
            build_chan_open_try_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        Some(self.src_chan_id),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_chan_id,
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawChanOpenAckCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[clap(required = true, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(
        short = 'd',
        long,
        required = true,
        help = "identifier of the destination channel (required)",
        value_name = "ID"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        short = 's',
        long,
        required = true,
        help = "identifier of the source channel (required)",
        value_name = "ID"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxRawChanOpenAckCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenAck",
            build_chan_open_ack_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        Some(self.src_chan_id),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id),
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawChanOpenConfirmCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[clap(required = true, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(
        short = 'd',
        long,
        required = true,
        help = "identifier of the destination channel (required)",
        value_name = "ID"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        short = 's',
        long,
        required = true,
        help = "identifier of the source channel (required)",
        value_name = "ID"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxRawChanOpenConfirmCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenConfirm",
            build_chan_open_confirm_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        Some(self.src_chan_id),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id),
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawChanCloseInitCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[clap(required = true, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(
        short = 'd',
        long,
        required = true,
        help = "identifier of the destination channel (required)",
        value_name = "ID"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        short = 's',
        long,
        required = true,
        help = "identifier of the source channel (required)",
        value_name = "ID"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxRawChanCloseInitCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanCloseInit",
            build_chan_close_init_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        Some(self.src_chan_id),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id),
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawChanCloseConfirmCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[clap(required = true, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[clap(required = true, help = "identifier of the source port")]
    src_port_id: PortId,

    #[clap(
        short = 'd',
        long,
        required = true,
        help = "identifier of the destination channel (required)",
        value_name = "ID"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        short = 's',
        long,
        required = true,
        help = "identifier of the source channel (required)",
        value_name = "ID"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxRawChanCloseConfirmCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanCloseConfirm",
            build_chan_close_confirm_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        Some(self.src_chan_id),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id),
                        None,
                    ),
                }
            }
        );
    }
}
