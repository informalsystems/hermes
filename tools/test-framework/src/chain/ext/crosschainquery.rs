use eyre::eyre;
use serde_json as json;
use std::time::Duration;

use crate::chain::cli::query::query_cross_chain_query;
use crate::error::Error;
use crate::prelude::{assert_eventually_succeed, handle_generic_error, ChainDriver};
use crate::types::tagged::MonoTagged;

/**
   Number of times (seconds) to try and query the list of cross chain
   queries.

   If you encounter retry error, verify the value of `stride_epoch`in
   the `stride_epoch` configuration in Stride's `genesis.toml` file.
*/
const WAIT_CROSS_CHAIN_QUERY_ATTEMPTS: u16 = 60;

pub trait CrossChainQueryMethodsExt<Chain> {
    fn assert_pending_cross_chain_query(&self) -> Result<(), Error>;

    fn assert_processed_cross_chain_query(&self) -> Result<(), Error>;
}

impl<'a, Chain: Send> CrossChainQueryMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn assert_pending_cross_chain_query(&self) -> Result<(), Error> {
        assert_eventually_succeed(
            "waiting for a cross chain query request",
            WAIT_CROSS_CHAIN_QUERY_ATTEMPTS,
            Duration::from_secs(1),
            || {
                let output = query_cross_chain_query(
                    self.0.chain_id.as_str(),
                    &self.0.command_path,
                    &self.0.rpc_listen_address(),
                )?;

                // Verify that there is at least one pending Cross Chain Query.
                let request_sent = json::from_str::<json::Value>(&output)
                    .map_err(handle_generic_error)?
                    .get("pending_queries")
                    .ok_or_else(|| eyre!("no pending cross chain queries"))?
                    .as_array()
                    .ok_or_else(|| eyre!("pending cross chain queries is not an array"))?
                    .first()
                    .ok_or_else(|| eyre!("no pending cross chain queries"))?
                    .as_bool();

                if let Some(sent) = request_sent {
                    if !sent {
                        return Err(Error::generic(eyre!("Request found but not sent")));
                    }
                }

                Ok(())
            },
        )?;

        Ok(())
    }

    fn assert_processed_cross_chain_query(&self) -> Result<(), Error> {
        assert_eventually_succeed(
            "waiting for the cross chain query to be relayed",
            WAIT_CROSS_CHAIN_QUERY_ATTEMPTS,
            Duration::from_secs(1),
            || {
                let output = query_cross_chain_query(
                    self.0.chain_id.as_str(),
                    &self.0.command_path,
                    &self.0.rpc_listen_address(),
                )?;

                // Verify that the there are no more pending Cross Chain Queries.
                if json::from_str::<json::Value>(&output)
                    .map_err(handle_generic_error)?
                    .get("pending_queries")
                    .ok_or_else(|| eyre!("no pending cross chain queries"))?
                    .as_array()
                    .ok_or_else(|| eyre!("pending cross chain queries is not an array"))?
                    .first()
                    .is_some()
                {
                    return Err(Error::generic(eyre!(
                        "Pending query has not been processed"
                    )));
                }

                Ok(())
            },
        )?;

        Ok(())
    }
}
