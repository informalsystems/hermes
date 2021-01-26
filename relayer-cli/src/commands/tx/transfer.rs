use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use relayer::{
    chain::{Chain, CosmosSDKChain},
    config::Config,
    transfer::{build_and_send_transfer_messages, TransferOptions},
};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawSendPacketCmd {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination chain")]
    dest_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, required, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(
        free,
        required,
        help = "amount of coins (samoleans, by default) to send (e.g. `100000`)"
    )]
    amount: u64,

    #[options(free, help = "timeout in number of blocks since current")]
    height_offset: u64,

    #[options(help = "denomination of the coins to send", short = "d")]
    denom: Option<String>,

    #[options(help = "number of messages to send", short = "n")]
    number_msgs: Option<usize>,
}

impl TxRawSendPacketCmd {
    fn validate_options(&self, config: &Config) -> Result<TransferOptions, String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id)
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dest_chain_config = config
            .find_chain(&self.dest_chain_id)
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let denom = self
            .denom
            .clone()
            .unwrap_or_else(|| "samoleans".to_string());
        let number_msgs = self.number_msgs.unwrap_or(1);
        if number_msgs == 0 {
            return Err("number of messages should be bigger than zero".to_string());
        }
        let opts = TransferOptions {
            packet_src_chain_config: src_chain_config.clone(),
            packet_dst_chain_config: dest_chain_config.clone(),
            packet_src_port_id: self.src_port_id.clone(),
            packet_src_channel_id: self.src_channel_id.clone(),
            amount: self.amount,
            denom,
            height_offset: self.height_offset,
            number_msgs,
        };

        Ok(opts)
    }
}

impl Runnable for TxRawSendPacketCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());

        let src_chain_res =
            CosmosSDKChain::bootstrap(opts.packet_src_chain_config.clone(), rt.clone())
                .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok(chain) => chain,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let dst_chain_res = CosmosSDKChain::bootstrap(opts.packet_dst_chain_config.clone(), rt)
            .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok(chain) => chain,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let res: Result<Vec<IBCEvent>, Error> =
            build_and_send_transfer_messages(src_chain, dst_chain, &opts)
                .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
