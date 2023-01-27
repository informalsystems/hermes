use core::str::FromStr;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use tendermint::Hash;

use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{QueryTxHash, QueryTxRequest};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::app_config;

/// Query the events emitted by transaction
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryTxEventsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "hash",
        required = true,
        value_name = "HASH",
        help_heading = "REQUIRED",
        help = "Transaction hash to query"
    )]
    hash: String,
}

// cargo run --bin hermes -- query tx events --chain ibc-0 --hash B8E78AD83810239E21863AC7B5FC4F99396ABB39EB534F721EEF43A4979C2821
impl Runnable for QueryTxEventsCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = Hash::from_str(self.hash.as_str())
            .map_err(|e| Error::invalid_hash(self.hash.clone(), e))
            .and_then(|h| {
                chain
                    .query_txs(QueryTxRequest::Transaction(QueryTxHash(h)))
                    .map_err(Error::relayer)
            });

        match res {
            Ok(res) => Output::success(res).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryTxEventsCmd;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_query_tx_events() {
        assert_eq!(
            QueryTxEventsCmd {
                chain_id: ChainId::from_string("chain_id"),
                hash: "abcdefg".to_owned()
            },
            QueryTxEventsCmd::parse_from(["test", "--chain", "chain_id", "--hash", "abcdefg"])
        )
    }

    #[test]
    fn test_query_tx_events_no_hash() {
        assert!(QueryTxEventsCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err())
    }

    #[test]
    fn test_query_tx_events_no_chain() {
        assert!(QueryTxEventsCmd::try_parse_from(["test", "--hash", "abcdefg"]).is_err())
    }
}
