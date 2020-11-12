use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ConnectionId, PortId, ChannelId};

use relayer::config::Config;

use crate::error::{Error, Kind};
use relayer::tx::channel::{ChannelOpenInitOptions, build_chan_init_and_send, build_chan_try_and_send, ChannelOpenTryOptions};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawChanInitCmd {
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

    #[options(help = "identifier of the source channel", short = "s")]
    src_channel_id: Option<ChannelId>,

    #[options(help = "the channel order", short = "o")]
    ordering: Order,

    #[options(
    help = "json key file for the signer, must include mnemonic",
    short = "k"
    )]
    seed_file: String,
}

impl TxRawChanInitCmd {
    fn validate_options(&self, config: &Config) -> Result<ChannelOpenInitOptions, String> {
        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let signer_seed = std::fs::read_to_string(&self.seed_file).map_err(|e| {
            anomaly::Context::new("invalid signer seed file", Some(e.into())).to_string()
        })?;

        let opts = ChannelOpenInitOptions {
            dest_chain_config: dest_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),

            dest_connection_id: self.dest_connection_id.clone(),

            dest_port_id: self.dest_port_id.clone(),
            src_port_id: self.src_port_id.clone(),

            dest_channel_id: self.dest_channel_id.clone(),
            src_channel_id: self.src_channel_id.clone(),

            ordering: self.ordering,
            signer_seed,
        };

        Ok(opts)
    }
}

impl Runnable for TxRawChanInitCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        let res: Result<String, Error> =
            build_chan_init_and_send(&opts).map_err(|e| Kind::Tx.context(e).into());

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

    #[options(
    help = "json key file for the signer, must include mnemonic",
    short = "k"
    )]
    seed_file: String,
}

impl TxRawChanTryCmd {
    fn validate_options(&self, config: &Config) -> Result<ChannelOpenTryOptions, String> {
        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let signer_seed = std::fs::read_to_string(&self.seed_file).map_err(|e| {
            anomaly::Context::new("invalid signer seed file", Some(e.into())).to_string()
        })?;

        let opts = ChannelOpenTryOptions {
            dest_chain_config: dest_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),

            dest_connection_id: self.dest_connection_id.clone(),

            dest_port_id: self.dest_port_id.clone(),
            src_port_id: self.src_port_id.clone(),

            dest_channel_id: self.dest_channel_id.clone(),
            src_channel_id: self.src_channel_id.clone(),

            ordering: self.ordering,
            signer_seed,
        };

        Ok(opts)
    }
}

impl Runnable for TxRawChanTryCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        let res: Result<String, Error> =
            build_chan_try_and_send(&opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("channel init, result: ", "{:?}", receipt),
            Err(e) => status_info!("channel init failed, error: ", "{}", e),
        }
    }
}