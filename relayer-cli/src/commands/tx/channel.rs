use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};

use relayer::config::ChainConfig;

use crate::error::{Error, Kind};
use relayer::channel::{
    build_chan_ack_and_send, build_chan_confirm_and_send, build_chan_init_and_send,
    build_chan_try_and_send,
};

use relayer::chain::runtime::ChainRuntime;
use relayer::channel::{ChannelConfig, ChannelConfigSide};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanInitCmd {
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

fn validate_common_options(
    dst_chain_id: &str,
    src_chain_id: &str,
) -> Result<(ChainConfig, ChainConfig), String> {
    let config = app_config();

    let dst_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == dst_chain_id.parse().unwrap())
        .ok_or_else(|| "missing destination chain configuration".to_string())?;

    let src_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == src_chain_id.parse().unwrap())
        .ok_or_else(|| "missing src chain configuration".to_string())?;

    Ok((dst_chain_config.clone(), src_chain_config.clone()))
}

impl Runnable for TxRawChanInitCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dst_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
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

        status_info!("Message ChanOpenInit", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_chan_init_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("channel init, result: ", "{:?}", receipt),
            Err(e) => status_info!("channel init failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanTryCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination connection")]
    dest_connection_id: ConnectionId,

    #[options(free, help = "identifier of the destination port")]
    dest_port_id: PortId,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination channel")]
    dest_channel_id: ChannelId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(help = "the channel order", short = "o")]
    ordering: Order,
}

impl Runnable for TxRawChanTryCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dest_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
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
                &self.dest_connection_id,
                &ClientId::default(),
                &self.src_port_id,
                &self.src_channel_id,
            ),
        };

        status_info!("Message ChanOpenTry", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_chan_try_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("channel try, result: ", "{:?}", receipt),
            Err(e) => status_info!("channel try failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanAckCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination connection")]
    dest_connection_id: ConnectionId,

    #[options(free, help = "identifier of the destination port")]
    dest_port_id: PortId,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination channel")]
    dest_channel_id: ChannelId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(help = "the channel order", short = "o")]
    ordering: Order,
}

impl Runnable for TxRawChanAckCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dest_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
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
                &self.dest_connection_id,
                &ClientId::default(),
                &self.src_port_id,
                &self.src_channel_id,
            ),
        };

        status_info!("Message ChanOpenAck", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_chan_ack_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("channel ack, result: ", "{:?}", receipt),
            Err(e) => status_info!("channel ack failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanConfirmCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination connection")]
    dest_connection_id: ConnectionId,

    #[options(free, help = "identifier of the destination port")]
    dest_port_id: PortId,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination channel")]
    dest_channel_id: ChannelId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(help = "the channel order", short = "o")]
    ordering: Order,
}

impl Runnable for TxRawChanConfirmCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dest_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
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
                &self.dest_connection_id,
                &ClientId::default(),
                &self.src_port_id,
                &self.src_channel_id,
            ),
        };

        status_info!("Message ChanOpenConfirm", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_chan_confirm_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());
        match res {
            Ok(receipt) => status_info!("channel confirm, result: ", "{:?}", receipt),
            Err(e) => status_info!("channel confirm failed, error: ", "{}", e),
        }
    }
}
