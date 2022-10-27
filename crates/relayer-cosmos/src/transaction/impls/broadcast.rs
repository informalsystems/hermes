use async_trait::async_trait;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::error::Error as RpcError;
use tendermint_rpc::Client;

use crate::transaction::traits::fields::{HasRpcAddress, HasRpcClient};

#[async_trait]
pub trait CanBroadcastTxSync: HasError {
    async fn broadcast_tx_sync(&self, data: Vec<u8>) -> Result<Response, Self::Error>;
}

#[async_trait]
impl<Context> CanBroadcastTxSync for Context
where
    Context: InjectError<RpcError> + HasRpcClient + HasRpcAddress,
{
    async fn broadcast_tx_sync(&self, data: Vec<u8>) -> Result<Response, Self::Error> {
        let rpc_client = self.rpc_client();

        let response = rpc_client
            .broadcast_tx_sync(data.into())
            .await
            .map_err(Context::inject_error)?;

        Ok(response)
    }
}
