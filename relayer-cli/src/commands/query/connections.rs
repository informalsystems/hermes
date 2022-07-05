use abscissa_core::clap::Parser;
use abscissa_core::Runnable;

use ibc::core::ics24_host::identifier::{ChainId, ConnectionId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{PageRequest, QueryConnectionsRequest};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct QueryConnectionsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,
}

// hermes query connections ibc-0
impl Runnable for QueryConnectionsCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_connections(QueryConnectionsRequest {
            pagination: Some(PageRequest::all()),
        });

        match res {
            Ok(connections) => {
                let ids: Vec<ConnectionId> = connections
                    .into_iter()
                    .map(|identified_connection| identified_connection.connection_id)
                    .collect();

                Output::success(ids).exit()
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryConnectionsCmd;

    use abscissa_core::clap::Parser;
    use ibc::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_query_connections() {
        assert_eq!(
            QueryConnectionsCmd {
                chain_id: ChainId::from_string("chain_id")
            },
            QueryConnectionsCmd::parse_from(&["test", "--chain", "chain_id"])
        )
    }

    #[test]
    fn test_query_connections_no_chain() {
        assert!(QueryConnectionsCmd::try_parse_from(&["test"]).is_err())
    }
}
