use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::Height;
use ibc_relayer::channel::{Channel, ChannelSide};
use ibc_relayer::config::StoreConfig;

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

macro_rules! tx_chan_cmd {
    ($dbg_string:literal, $func:ident, $self:expr, $chan:expr) => {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());
        let chains = match ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &$self.src_chain_id,
            &$self.dst_chain_id,
        ) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains
            .dst
            .query_connection(&$self.dst_conn_id, Height::default())
        {
            Ok(connection) => connection,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let channel = $chan(chains, dst_connection);

        info!("Message {}: {:?}", $dbg_string, channel);

        let res: Result<IBCEvent, Error> = channel.$func().map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    };
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanOpenInitCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,
}

impl Runnable for TxRawChanOpenInitCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenInit",
            build_chan_open_init_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        ChannelId::default(),
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        ChannelId::default(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanOpenTryCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(
        required,
        help = "identifier of the source channel (required)",
        short = "s",
        meta = "ID"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxRawChanOpenTryCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenTry",
            build_chan_open_try_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        self.src_chan_id.clone(),
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        ChannelId::default(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanOpenAckCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(
        required,
        help = "identifier of the destination channel (required)",
        short = "d",
        meta = "ID"
    )]
    dst_chan_id: ChannelId,

    #[options(
        required,
        help = "identifier of the source channel (required)",
        short = "s",
        meta = "ID"
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
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        self.src_chan_id.clone(),
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_chan_id.clone(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanOpenConfirmCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(
        required,
        help = "identifier of the destination channel (required)",
        short = "d",
        meta = "ID"
    )]
    dst_chan_id: ChannelId,

    #[options(
        required,
        help = "identifier of the source channel (required)",
        short = "s",
        meta = "ID"
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
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        self.src_chan_id.clone(),
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_chan_id.clone(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanCloseInitCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(
        required,
        help = "identifier of the destination channel (required)",
        short = "d",
        meta = "ID"
    )]
    dst_chan_id: ChannelId,

    #[options(
        required,
        help = "identifier of the source channel (required)",
        short = "s",
        meta = "ID"
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
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        self.src_chan_id.clone(),
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_chan_id.clone(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanCloseConfirmCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination connection")]
    dst_conn_id: ConnectionId,

    #[options(free, required, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(
        required,
        help = "identifier of the destination channel (required)",
        short = "d",
        meta = "ID"
    )]
    dst_chan_id: ChannelId,

    #[options(
        required,
        help = "identifier of the source channel (required)",
        short = "s",
        meta = "ID"
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
                    ordering: Order::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        self.src_chan_id.clone(),
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_chan_id.clone(),
                    ),
                }
            }
        );
    }
}
