use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasError;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::transaction::impls::broadcast::CanBroadcastTxSync;
use crate::transaction::impls::encode::CanSignAndEncodeTx;
use crate::transaction::traits::tx_sender::CanSubmitTxWithFee;

#[async_trait]
impl<Context> CanSubmitTxWithFee for Context
where
    Context: HasError + CanSignAndEncodeTx + CanBroadcastTxSync,
{
    async fn submit_tx_with_fee(
        &self,
        messages: &[Any],
        fee: &Fee,
    ) -> Result<Response, Self::Error> {
        let tx_bytes = self.sign_and_encode_tx(messages, fee).await?;

        let response = self.broadcast_tx_sync(tx_bytes).await?;

        Ok(response)
    }
}
