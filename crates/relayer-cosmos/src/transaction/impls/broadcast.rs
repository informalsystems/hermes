use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::TxRaw;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use prost::EncodeError;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::error::Error as RpcError;
use tendermint_rpc::Client;

use crate::transaction::traits::fields::{HasRpcAddress, HasRpcClient};

#[async_trait]
pub trait CanBroadcastTxSync: HasError {
    async fn broadcast_tx_sync(&self, tx: SignedTx) -> Result<Response, Self::Error>;
}

#[async_trait]
impl<Context> CanBroadcastTxSync for Context
where
    Context: InjectError<RpcError> + InjectError<EncodeError> + HasRpcClient + HasRpcAddress,
{
    async fn broadcast_tx_sync(&self, tx: SignedTx) -> Result<Response, Self::Error> {
        let rpc_client = self.rpc_client();

        let data = {
            let tx_raw = TxRaw {
                body_bytes: tx.body_bytes,
                auth_info_bytes: tx.auth_info_bytes,
                signatures: tx.signatures,
            };

            let mut tx_bytes = Vec::new();

            prost::Message::encode(&tx_raw, &mut tx_bytes).map_err(Context::inject_error)?;

            tx_bytes
        };

        let response = rpc_client
            .broadcast_tx_sync(data)
            .await
            .map_err(Context::inject_error)?;

        Ok(response)
    }
}
