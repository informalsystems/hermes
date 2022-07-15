use abscissa_core::clap::Parser;
use abscissa_core::{config::Override, Command, FrameworkErrorKind, Runnable};

use core::time::Duration;
use ibc::{
    applications::transfer::Amount,
    core::{
        ics02_client::client_state::ClientState,
        ics24_host::identifier::{ChainId, ChannelId, PortId},
    },
    events::IbcEvent,
};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, QueryChannelRequest, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use ibc_relayer::{
    config::Config,
    transfer::{build_and_send_transfer_messages, TransferOptions},
};

use crate::cli_utils::ChainHandlePair;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct TxIcs20MsgTransferCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "src-port",
        required = true,
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "src-channel",
        alias = "src-chan",
        required = true,
        help = "Identifier of the source channel"
    )]
    src_channel_id: ChannelId,

    #[clap(
        long = "amount",
        required = true,
        help = "Amount of coins (samoleans, by default) to send (e.g. `100000`)"
    )]
    amount: Amount,

    #[clap(
        long = "timeout-height-offset",
        default_value = "0",
        help = "Timeout in number of blocks since current"
    )]
    timeout_height_offset: u64,

    #[clap(
        long = "timeout-seconds",
        default_value = "0",
        help = "Timeout in seconds since current"
    )]
    timeout_seconds: u64,

    #[clap(
        long = "receiver",
        help = "The account address on the destination chain which will receive the tokens. If omitted, the relayer's wallet on the destination chain will be used"
    )]
    receiver: Option<String>,

    #[clap(
        long = "denom",
        help = "Denomination of the coins to send",
        default_value = "samoleans"
    )]
    denom: String,

    #[clap(long = "number-msgs", help = "Number of messages to send")]
    number_msgs: Option<usize>,

    #[clap(
        long = "key-name",
        help = "Use the given signing key name (default: `key_name` config)"
    )]
    key_name: Option<String>,
}

impl Override<Config> for TxIcs20MsgTransferCmd {
    fn override_config(&self, mut config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        let src_chain_config = config.find_chain_mut(&self.src_chain_id).ok_or_else(|| {
            FrameworkErrorKind::ComponentError.context(format!(
                "missing configuration for source chain '{}'",
                self.src_chain_id
            ))
        })?;

        if let Some(ref key_name) = self.key_name {
            src_chain_config.key_name = key_name.to_string();
        }

        Ok(config)
    }
}

impl TxIcs20MsgTransferCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<TransferOptions, Box<dyn std::error::Error>> {
        config.find_chain(&self.src_chain_id).ok_or_else(|| {
            format!(
                "missing configuration for source chain '{}'",
                self.src_chain_id
            )
        })?;

        config.find_chain(&self.dst_chain_id).ok_or_else(|| {
            format!(
                "missing configuration for destination chain '{}'",
                self.dst_chain_id
            )
        })?;

        let denom = self.denom.clone();

        let number_msgs = self.number_msgs.unwrap_or(1);
        if number_msgs == 0 {
            return Err("number of messages should be greater than zero".into());
        }

        let opts = TransferOptions {
            packet_src_port_id: self.src_port_id.clone(),
            packet_src_channel_id: self.src_channel_id.clone(),
            amount: self.amount,
            denom,
            receiver: self.receiver.clone(),
            timeout_height_offset: self.timeout_height_offset,
            timeout_duration: Duration::from_secs(self.timeout_seconds),
            number_msgs,
        };

        Ok(opts)
    }
}

impl Runnable for TxIcs20MsgTransferCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => Output::error(err).exit(),
            Ok(result) => result,
        };

        debug!("Message: {:?}", opts);

        let chains = ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Double check that channels and chain identifiers match.
        // To do this, fetch from the source chain the channel end, then the associated connection
        // end, and then the underlying client state; finally, check that this client is verifying
        // headers for the destination chain.
        let (channel_end_src, _) = chains
            .src
            .query_channel(
                QueryChannelRequest {
                    port_id: opts.packet_src_port_id.clone(),
                    channel_id: opts.packet_src_channel_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .unwrap_or_else(exit_with_unrecoverable_error);
        if !channel_end_src.is_open() {
            Output::error(format!(
                "the requested port/channel ('{}'/'{}') on chain id '{}' is in state '{}'; expected 'open' state",
                opts.packet_src_port_id,
                opts.packet_src_channel_id,
                self.src_chain_id,
                channel_end_src.state
            ))
                .exit();
        }

        let conn_id = match channel_end_src.connection_hops.first() {
            None => {
                Output::error(format!(
                    "could not retrieve the connection hop underlying port/channel '{}'/'{}' on chain '{}'",
                    opts.packet_src_port_id, opts.packet_src_channel_id, self.src_chain_id
                ))
                    .exit();
            }
            Some(cid) => cid,
        };

        let (conn_end, _) = chains
            .src
            .query_connection(
                QueryConnectionRequest {
                    connection_id: conn_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .unwrap_or_else(exit_with_unrecoverable_error);

        debug!("connection hop underlying the channel: {:?}", conn_end);

        let (src_chain_client_state, _) = chains
            .src
            .query_client_state(
                QueryClientStateRequest {
                    client_id: conn_end.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .unwrap_or_else(exit_with_unrecoverable_error);

        debug!(
            "client state underlying the channel: {:?}",
            src_chain_client_state
        );

        if src_chain_client_state.chain_id() != self.dst_chain_id {
            Output::error(
                format!("the requested port/channel ('{}'/'{}') provides a path from chain '{}' to \
                 chain '{}' (not to the destination chain '{}'). Bailing due to mismatching arguments.",
                        opts.packet_src_port_id, opts.packet_src_channel_id,
                        self.src_chain_id,
                        src_chain_client_state.chain_id(), self.dst_chain_id)).exit();
        }

        // Checks pass, build and send the tx
        let res: Result<Vec<IbcEvent>, Error> =
            build_and_send_transfer_messages(&chains.src, &chains.dst, &opts)
                .map_err(Error::transfer);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
