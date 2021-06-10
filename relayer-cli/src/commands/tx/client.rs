use abscissa_core::{Command, Options, Runnable};

use ibc::events::IbcEvent;
use ibc::ics02_client::client_state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::util::retry::retry_recoverable_with_index;

use crate::application::app_config;
use crate::cli_utils::{spawn_chain_runtime, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::{Error, Kind};

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,
}

/// Sample to run this tx:
///     `hermes tx raw create-client ibc-0 ibc-1`
impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let config = app_config();

        if self.src_chain_id == self.dst_chain_id {
            Output::error("source and destination chains must be different".to_string()).exit()
        }

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::restore(ClientId::default(), chains.dst, chains.src);

        // Trigger client creation via the "build" interface, so that we obtain the resulting event
        let res: Result<IbcEvent, Error> = client
            .build_create_client_and_send()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(
        free,
        required,
        help = "identifier of the client to be updated on destination chain"
    )]
    dst_client_id: ClientId,

    #[options(help = "the target height of the client update", short = "h")]
    target_height: Option<u64>,

    #[options(help = "the trusted height of the client update", short = "t")]
    trusted_height: Option<u64>,

    #[options(
        help = "retry the operation if fails with recoverable error",
        short = "r"
    )]
    retry: bool,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        mod retry_strategy {
            use ibc_relayer::util::retry::clamp_total;
            use retry::delay::Fibonacci;
            use std::time::Duration;

            // Default parameters for the retrying mechanism
            const MAX_DELAY: Duration = Duration::from_secs(10); // 10 seconds
            const MAX_TOTAL_DELAY: Duration = Duration::from_secs(60); // 1 minute
            const INITIAL_DELAY: Duration = Duration::from_secs(1); // 1 second

            pub fn default() -> impl Iterator<Item = Duration> {
                clamp_total(Fibonacci::from(INITIAL_DELAY), MAX_DELAY, MAX_TOTAL_DELAY)
            }
        }

        fn do_run(ctx: &TxUpdateClientCmd) -> Result<Vec<IbcEvent>, Error> {
            let config = app_config();

            let dst_chain = spawn_chain_runtime(&config, &ctx.dst_chain_id)?;

            let src_chain_id = dst_chain
                .query_client_state(&ctx.dst_client_id, ibc::Height::zero())
                .map_err(|e| Kind::Relayer(e.kind().clone()).context(e))?
                .chain_id();

            let src_chain = spawn_chain_runtime(&config, &src_chain_id)?;

            let height = match ctx.target_height {
                Some(height) => ibc::Height::new(src_chain.id().version(), height),
                None => ibc::Height::zero(),
            };

            let trusted_height = match ctx.trusted_height {
                Some(height) => ibc::Height::new(src_chain.id().version(), height),
                None => ibc::Height::zero(),
            };

            let client = ForeignClient::find(src_chain, dst_chain, &ctx.dst_client_id)
                .map_err(|e| Kind::ForeignClient(e.clone()).context(e))?;

            client
                .build_update_client_and_send(height, trusted_height)
                .map_err(|e| Kind::ForeignClient(e.clone()).context(e).into())
        }

        if self.retry {
            let res = retry_recoverable_with_index(
                "run_update_client",
                retry_strategy::default(),
                |_| do_run(self),
            );

            match res {
                Ok(events) => Output::success(events).exit(),
                Err(e) => Output::error(format!("{}", e)).exit(),
            }
        } else {
            let res = do_run(self);

            match res {
                Ok(events) => Output::success(events).exit(),
                Err(e) => Output::error(format!("{}", e)).exit(),
            }
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpgradeClientCmd {
    #[options(free, required, help = "identifier of the chain that hosts the client")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to be upgraded")]
    client_id: ClientId,
}

impl Runnable for TxUpgradeClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id = match dst_chain.query_client_state(&self.client_id, ibc::Height::zero())
        {
            Ok(cs) => cs.chain_id(),
            Err(e) => {
                return Output::error(format!(
                    "Query of client '{}' on chain '{}' failed with error: {}",
                    self.client_id, self.chain_id, e
                ))
                .exit()
            }
        };

        let src_chain = match spawn_chain_runtime(&config, &src_chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::find(src_chain, dst_chain, &self.client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let outcome = client.upgrade();

        match outcome {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
