use crate::prelude::*;
use std::sync::{Arc, Mutex};
use tokio::runtime::Runtime as TokioRuntime;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;

use crate::error::{Error, Kind};
use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use relayer::chain::{Chain, CosmosSDKChain};
use relayer::transfer::{build_and_send_transfer_messages, TransferOptions};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawSendPacketCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(free, help = "amount of samoleans to send (e.g. `100000`)")]
    amount: u64,

    #[options(free, help = "timeout in number of blocks since current")]
    height_offset: u64,

    #[options(help = "number of messages to send", short = "n")]
    number_msgs: Option<usize>,
}

impl TxRawSendPacketCmd {
    fn validate_options(&self, config: &Config) -> Result<TransferOptions, String> {
        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = TransferOptions {
            packet_src_chain_config: src_chain_config.clone(),
            packet_dst_chain_config: dest_chain_config.clone(),
            packet_src_port_id: self.src_port_id.clone(),
            packet_src_channel_id: self.src_channel_id.clone(),
            amount: self.amount,
            height_offset: self.height_offset,
            number_msgs: self.number_msgs.unwrap_or(1),
        };

        Ok(opts)
    }
}

impl Runnable for TxRawSendPacketCmd {
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

        let rt = Arc::new(Mutex::new(TokioRuntime::new().unwrap()));
        let src_chain =
            CosmosSDKChain::bootstrap(opts.packet_src_chain_config.clone(), rt.clone()).unwrap();
        let dst_chain =
            CosmosSDKChain::bootstrap(opts.packet_dst_chain_config.clone(), rt).unwrap();

        let res: Result<Vec<IBCEvent>, Error> =
            build_and_send_transfer_messages(src_chain, dst_chain, &opts)
                .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => status_info!(
                "packet recv, result: ",
                "{:#?}",
                serde_json::to_string(&ev).unwrap()
            ),
            Err(e) => status_info!("packet recv failed, error: ", "{}", e),
        }
    }
}
