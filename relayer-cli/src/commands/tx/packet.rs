use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use relayer::config::{ChainConfig, Config};
use relayer::link::{Link, ChannelParameters};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketRecvCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(free, help = "identifier of the destination channel")]
    dst_channel_id: ChannelId,
}

impl TxRawPacketRecvCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, ChainConfig, ChannelParameters), String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dst_chain_config = config
            .find_chain(&self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = ChannelParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
            dst_port_id: self.dst_port_id.clone(),
            dst_channel_id: self.dst_channel_id.clone(),
        };

        Ok((dst_chain_config.clone(), src_chain_config.clone(), opts))
    }
}

impl Runnable for TxRawPacketRecvCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };
        let mut link = Link::new_from_opts(src_chain, dst_chain, &opts).unwrap();

        let res: Result<Vec<IBCEvent>, Error> = link
            .build_and_send_recv_packet_messages()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketAckCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(free, help = "identifier of the destination channel")]
    dst_channel_id: ChannelId,
}

impl TxRawPacketAckCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, ChainConfig, ChannelParameters), String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dst_chain_config = config
            .find_chain(&self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = ChannelParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
            dst_port_id: self.dst_port_id.clone(),
            dst_channel_id: self.dst_channel_id.clone(),
        };

        Ok((dst_chain_config.clone(), src_chain_config.clone(), opts))
    }
}

impl Runnable for TxRawPacketAckCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };
        let mut link = Link::new_from_opts(src_chain, dst_chain, &opts).unwrap();
        let res: Result<Vec<IBCEvent>, Error> = link
            .build_and_send_ack_packet_messages()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
