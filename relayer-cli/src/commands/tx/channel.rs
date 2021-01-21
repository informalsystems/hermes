use abscissa_core::{Command, Options, Runnable};
use serde_json::json;

use ibc::events::IBCEvent;
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::Height;
use relayer::chain::{runtime::ChainRuntime, CosmosSDKChain};
use relayer::channel::{Channel, ChannelSide};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

macro_rules! chan_open_cmd {
    ($chan_open_cmd:ident, $dbg_string:literal, $func:ident) => {
        #[derive(Clone, Command, Debug, Options)]
        pub struct $chan_open_cmd {
            #[options(free, help = "identifier of the destination chain")]
            dst_chain_id: String,

            #[options(free, help = "identifier of the source chain")]
            src_chain_id: String,

            #[options(free, help = "identifier of the destination connection")]
            dst_connection_id: ConnectionId,

            #[options(free, help = "identifier of the destination port")]
            dst_port_id: PortId,

            #[options(free, help = "identifier of the source port")]
            src_port_id: PortId,

            #[options(free, help = "identifier of the destination channel")]
            dst_channel_id: ChannelId,

            #[options(free, help = "identifier of the source channel")]
            src_channel_id: ChannelId,

            #[options(help = "the channel order", short = "o")]
            ordering: Order,
        }

        impl Runnable for $chan_open_cmd {
            fn run(&self) {
                let config = app_config();

                let src_config = config
                    .find_chain(&self.src_chain_id.parse().unwrap())
                    .ok_or_else(|| "missing src chain configuration".to_string());

                let dst_config = config
                    .find_chain(&self.dst_chain_id.parse().unwrap())
                    .ok_or_else(|| "missing src chain configuration".to_string());

                let (src_chain_config, dst_chain_config) = match (src_config, dst_config) {
                    (Ok(s), Ok(d)) => (s, d),
                    (_, _) => {
                        return Output::error(json!(
                            "error occurred in finding the chains' configuration"
                        ))
                        .exit();
                    }
                };

                let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config.clone())
                    .map_err(|e| Kind::Runtime.context(e));
                let src_chain = match src_chain_res {
                    Ok((handle, _)) => handle,
                    Err(e) => {
                        return Output::error(format!("{}", e)).exit();
                    }
                };

                let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config.clone())
                    .map_err(|e| Kind::Runtime.context(e));
                let dst_chain = match dst_chain_res {
                    Ok((handle, _)) => handle,
                    Err(e) => {
                        return Output::error(format!("{}", e)).exit();
                    }
                };

                // Retrieve the connection
                let dst_connection = dst_chain
                    .query_connection(&self.dst_connection_id, Height::default())
                    .unwrap();

                let channel = Channel {
                    ordering: self.ordering,
                    a_side: ChannelSide::new(
                        src_chain,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        self.src_channel_id.clone(),
                    ),
                    b_side: ChannelSide::new(
                        dst_chain,
                        dst_connection.client_id().clone(),
                        self.dst_connection_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_channel_id.clone(),
                    ),
                };

                info!("Message {}: {:?}", $dbg_string, channel);

                let res: Result<IBCEvent, Error> =
                    channel.$func().map_err(|e| Kind::Tx.context(e).into());

                match res {
                    Ok(receipt) => Output::success(receipt).exit(),
                    Err(e) => Output::error(format!("{}", e)).exit(),
                }
            }
        }
    };
}

chan_open_cmd!(TxRawChanInitCmd, "ChanOpenInit", build_chan_init_and_send);

chan_open_cmd!(TxRawChanTryCmd, "ChanOpenTry", build_chan_try_and_send);

chan_open_cmd!(TxRawChanAckCmd, "ChanOpenAck", build_chan_ack_and_send);

chan_open_cmd!(
    TxRawChanConfirmCmd,
    "ChanOpenConfirm",
    build_chan_confirm_and_send
);
