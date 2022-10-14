use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::error::Error as RpcError;
use tendermint_rpc::Client;

use crate::transaction::impls::encode::CanSignAndEncodeTx;
use crate::transaction::impls::estimate::CanEstimateTxFees;
use crate::transaction::impls::keys;
use crate::transaction::traits::field::{FieldGetter, HasField};

#[async_trait]
pub trait CanEstimateFeeAndSendTx: HasError {
    async fn estimate_fee_and_send_tx(&self, messages: &[Any]) -> Result<Response, Self::Error>;
}

#[async_trait]
impl<Context> CanEstimateFeeAndSendTx for Context
where
    Context: HasError + CanEstimateTxFees + CanSendTxWithFee,
{
    async fn estimate_fee_and_send_tx(&self, messages: &[Any]) -> Result<Response, Self::Error> {
        let fee = self.estimate_tx_fees(messages).await?;

        self.send_tx_with_fee(messages, &fee).await
    }
}

#[async_trait]
pub trait CanSendTxWithFee: HasError {
    async fn send_tx_with_fee(&self, messages: &[Any], fee: &Fee) -> Result<Response, Self::Error>;
}

#[async_trait]
impl<Context> CanSendTxWithFee for Context
where
    Context: HasError + CanSignAndEncodeTx + CanBroadcastTxSync,
{
    async fn send_tx_with_fee(&self, messages: &[Any], fee: &Fee) -> Result<Response, Self::Error> {
        let tx_bytes = self.sign_and_encode_tx(messages, fee)?;

        let response = self.broadcast_tx_sync(tx_bytes).await?;

        Ok(response)
    }
}

#[async_trait]
pub trait CanBroadcastTxSync: HasError {
    async fn broadcast_tx_sync(&self, data: Vec<u8>) -> Result<Response, Self::Error>;
}

#[async_trait]
impl<Context> CanBroadcastTxSync for Context
where
    Context: InjectError<RpcError> + HasField<keys::RpcClient> + HasField<keys::RpcAddress>,
{
    async fn broadcast_tx_sync(&self, data: Vec<u8>) -> Result<Response, Self::Error> {
        let rpc_client = keys::RpcClient::get_from(self);

        let response = rpc_client
            .broadcast_tx_sync(data.into())
            .await
            .map_err(Context::inject_error)?;

        Ok(response)
    }
}
