use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};

use crate::error::{Error, Kind};
use relayer::channel::{
    build_chan_ack_and_send, build_chan_confirm_and_send, build_chan_init_and_send,
    build_chan_try_and_send,
};

use relayer::chain::runtime::ChainRuntime;
use relayer::channel::{ChannelConfig, ChannelConfigSide};

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
                    .chains
                    .iter()
                    .find(|c| c.id == self.src_chain_id.parse().unwrap())
                    .ok_or_else(|| "missing src chain configuration".to_string());

                let dst_config = config
                    .chains
                    .iter()
                    .find(|c| c.id == self.dst_chain_id.parse().unwrap())
                    .ok_or_else(|| "missing src chain configuration".to_string());

                let (src_chain_config, dst_chain_config) = match (src_config, dst_config) {
                    (Ok(s), Ok(d)) => (s, d),
                    (_, _) => {
                        status_err!("invalid options");
                        return;
                    }
                };

                let opts = ChannelConfig {
                    ordering: self.ordering,
                    src_config: ChannelConfigSide::new(
                        &src_chain_config.id,
                        &ConnectionId::default(),
                        &ClientId::default(),
                        &self.src_port_id,
                        &self.src_channel_id,
                    ),
                    dst_config: ChannelConfigSide::new(
                        &dst_chain_config.id,
                        &self.dst_connection_id,
                        &ClientId::default(),
                        &self.src_port_id,
                        &self.src_channel_id,
                    ),
                };

                status_info!("Message $dbg_string", "{:#?}", opts);

                let (src_chain, _) = ChainRuntime::spawn(src_chain_config.clone()).unwrap();
                let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config.clone()).unwrap();

                let res: Result<String, Error> =
                    $func(dst_chain, src_chain, &opts).map_err(|e| Kind::Tx.context(e).into());

                match res {
                    Ok(receipt) => status_info!("$dbg_string, result: ", "{:?}", receipt),
                    Err(e) => status_info!("$dbg_string failed, error: ", "{}", e),
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
