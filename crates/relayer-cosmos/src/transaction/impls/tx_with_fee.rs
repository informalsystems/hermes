use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasError;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::transaction::impls::broadcast::CanBroadcastTxSync;
use crate::transaction::impls::encode::CanSignAndEncodeTx;
use ibc_relayer::chain::cosmos::types::account::AccountSequence;

#[async_trait]
pub trait CanSubmitTxWithFee: HasError {
    async fn submit_tx_with_fee(
        &self,
        fee: &Fee,
        sequence: &AccountSequence,
        messages: &[Any],
    ) -> Result<Response, Self::Error>;
}

#[async_trait]
impl<Context> CanSubmitTxWithFee for Context
where
    Context: HasError + CanSignAndEncodeTx + CanBroadcastTxSync,
{
    async fn submit_tx_with_fee(
        &self,
        fee: &Fee,
        sequence: &AccountSequence,
        messages: &[Any],
    ) -> Result<Response, Self::Error> {
        let tx_bytes = self.sign_and_encode_tx(fee, sequence, messages).await?;

        let response = self.broadcast_tx_sync(tx_bytes).await?;

        Ok(response)
    }
}
