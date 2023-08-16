use async_trait::async_trait;
use ibc_relayer::chain::cosmos::query::tx::query_tx_response;
use ibc_relayer_components::transaction::traits::response::query::TxResponseQuerier;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;

use crate::contexts::transaction::CosmosTxContext;
use crate::impls::transaction::component::CosmosTxComponents;
use crate::types::error::{BaseError, Error};

#[async_trait]
impl TxResponseQuerier<CosmosTxContext> for CosmosTxComponents {
    async fn query_tx_response(
        context: &CosmosTxContext,
        tx_hash: &TxHash,
    ) -> Result<Option<TxResponse>, Error> {
        let tx_config = &context.tx_config;
        let rpc_client = &context.rpc_client;

        let response = query_tx_response(rpc_client, &tx_config.rpc_address, tx_hash)
            .await
            .map_err(BaseError::relayer)?;

        Ok(response)
    }
}
