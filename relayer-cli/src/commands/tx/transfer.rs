use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use anomaly::BoxError;
use tokio::runtime::Runtime as TokioRuntime;

use ibc::events::IbcEvent;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::{
    chain::{Chain, CosmosSdkChain},
    config::Config,
    transfer::{build_and_send_transfer_messages, TransferOptions},
};

use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxIcs20MsgTransferCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

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

    #[options(free, required, help = "timeout in number of blocks since current")]
    height_offset: u64,

    #[options(
        help = "receiving account address on the destination chain",
        short = "r"
    )]
    receiver: Option<String>,

    #[options(
        help = "denomination of the coins to send",
        short = "d",
        default = "samoleans"
    )]
    denom: String,

    #[options(help = "number of messages to send", short = "n")]
    number_msgs: Option<usize>,
}

impl TxIcs20MsgTransferCmd {
    fn validate_options(&self, config: &Config) -> Result<TransferOptions, BoxError> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id)
            .ok_or("missing src chain configuration")?;

        let dest_chain_config = config
            .find_chain(&self.dst_chain_id)
            .ok_or("missing destination chain configuration")?;

        let denom = self.denom.clone();

        let number_msgs = self.number_msgs.unwrap_or(1);
        if number_msgs == 0 {
            return Err("number of messages should be greater than zero".into());
        }

        let opts = TransferOptions {
            packet_src_chain_config: src_chain_config.clone(),
            packet_dst_chain_config: dest_chain_config.clone(),
            packet_src_port_id: self.src_port_id.clone(),
            packet_src_channel_id: self.src_channel_id.clone(),
            amount: self.amount,
            denom,
            receiver: self.receiver.clone(),
            height_offset: self.height_offset,
            number_msgs,
        };

        Ok(opts)
    }
}

impl Runnable for TxIcs20MsgTransferCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        debug!("Message: {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());

        let src_chain_res =
            CosmosSdkChain::bootstrap(opts.packet_src_chain_config.clone(), rt.clone())
                .map_err(|e| Kind::Runtime.context(e));

        let src_chain = match src_chain_res {
            Ok(chain) => chain,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let dst_chain_res = CosmosSdkChain::bootstrap(opts.packet_dst_chain_config.clone(), rt)
            .map_err(|e| Kind::Runtime.context(e));

        let dst_chain = match dst_chain_res {
            Ok(chain) => chain,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        // Double check that channels and chain identifiers match.
        // To do this, fetch from the source chain the channel end, then the associated connection
        // end, and then the underlying client state; finally, check that this client is verifying
        // headers for the destination chain.
        let channel_end = src_chain
            .query_channel(
                &opts.packet_src_port_id,
                &opts.packet_src_channel_id,
                Height::zero(),
            )
            .unwrap_or_else(exit_with_unrecoverable_error);
        // TODO: Support for multi-hop channels will impact this.
        let conn_id = match channel_end.connection_hops.first() {
            None => {
                return Output::error(format!(
                    "could not retrieve the connection hop underlying port/channel '{}'/'{}' on chain '{}'",
                    opts.packet_src_port_id, opts.packet_src_channel_id, self.src_chain_id
                ))
                .exit()
            }
            Some(cid) => cid,
        };
        let conn_end = src_chain
            .query_connection(conn_id, Height::zero())
            .unwrap_or_else(exit_with_unrecoverable_error);
        debug!("connection hop underlying the channel: {:?}", conn_end);
        let src_chain_client_state = src_chain
            .query_client_state(conn_end.client_id(), Height::zero())
            .unwrap_or_else(exit_with_unrecoverable_error);
        debug!(
            "client state underlying the channel: {:?}",
            src_chain_client_state
        );
        if src_chain_client_state.chain_id != self.dst_chain_id {
            return Output::error(
                format!("the requested port/channel ({}/{}) provides a path from chain '{}' to \
                 chain '{}' (not to the destination chain '{}'). Bailing due to mismatching arguments.",
                        opts.packet_src_port_id, opts.packet_src_channel_id,
                        self.src_chain_id,
                        src_chain_client_state.chain_id, self.dst_chain_id)).exit();
        }

        // Checks pass, build and send the tx
        let res: Result<Vec<IbcEvent>, Error> =
            build_and_send_transfer_messages(src_chain, dst_chain, opts)
                .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
