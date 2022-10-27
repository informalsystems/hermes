use async_trait::async_trait;
use ibc_relayer::chain::cosmos::query::tx_hash_query;
use ibc_relayer::chain::requests::QueryTxHash;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use tendermint::abci::transaction::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::{Client, Error as RpcError, Order};

use crate::transaction::traits::fields::{HasRpcClient, HasWaitTimeout};

#[async_trait]
pub trait CanQueryTxResponse: HasError {
    async fn query_tx_response(&self, tx_hash: &TxHash) -> Result<Option<TxResponse>, Self::Error>;
}

#[async_trait]
impl<Context> CanQueryTxResponse for Context
where
    Context: InjectError<RpcError>,
    Context: HasRpcClient + HasWaitTimeout,
{
    async fn query_tx_response(&self, tx_hash: &TxHash) -> Result<Option<TxResponse>, Self::Error> {
        let rpc_client = self.rpc_client();

        let response = rpc_client
            .tx_search(
                tx_hash_query(&QueryTxHash(*tx_hash)),
                false,
                1,
                1, // get only the first Tx matching the query
                Order::Ascending,
            )
            .await
            .map_err(Self::inject_error)?;

        Ok(response.txs.into_iter().next())
    }
}
