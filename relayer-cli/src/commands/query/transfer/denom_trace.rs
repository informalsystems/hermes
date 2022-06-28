use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, json, Output};

/// The data structure that represents the arguments when invoking the `query transfer denom-trace` CLI command.
///
/// The command has the following format:
///
/// `query transfer denom-trace --chain <CHAIN_ID> --hash <HASH>`
///
/// If successful the the base denomination and the path will be displayed.
#[derive(Clone, Command, Debug, Parser)]
pub struct DenomTraceCmd {
    #[clap(long = "chain", required = true, help = "Identifier of the chain")]
    chain_id: ChainId,

    #[clap(long = "hash", required = true, help = "Trace hash to query")]
    hash: String,
}

impl Runnable for DenomTraceCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        match chain.query_denom_trace(self.hash.clone()) {
            Ok(denom_trace) if json() => Output::success(denom_trace).exit(),
            Ok(denom_trace) => Output::success_msg(format!(
                "base_denom: {}\n path: {}",
                denom_trace.base_denom, denom_trace.path
            ))
            .exit(),
            Err(e) => Output::error(format!(
                "there was a problem querying the denomination trace: {}",
                e
            ))
            .exit(),
        }
    }
}
