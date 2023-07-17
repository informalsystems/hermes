use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;

use crate::contexts::chain::CosmosChain;
use crate::types::error::{BaseError, Error};

pub async fn query_chain_status<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
) -> Result<ChainStatus, Error> {
    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let status = chain_handle
                .query_application_status()
                .map_err(BaseError::relayer)?;

            Ok(status)
        })
        .await
        .map_err(BaseError::join)?
}
