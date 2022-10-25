use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasError;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::transaction::impls::broadcast::CanBroadcastTxSync;
use crate::transaction::impls::encode::CanSignAndEncodeTx;
use crate::transaction::impls::estimate::CanEstimateTxFees;

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
        let tx_bytes = self.sign_and_encode_tx(messages, fee).await?;

        let response = self.broadcast_tx_sync(tx_bytes).await?;

        Ok(response)
    }
}
