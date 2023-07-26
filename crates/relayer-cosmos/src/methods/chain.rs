use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::types::error::{BaseError, Error};

pub async fn query_chain_status<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
) -> Result<ChainStatus, Error> {
    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let status = chain_handle
                .query_application_status()
                .map_err(BaseError::relayer)?;

            Ok(status)
        })
        .await
}
