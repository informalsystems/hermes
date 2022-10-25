use async_trait::async_trait;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasError;
use tendermint::abci::responses::Event;

#[async_trait]
pub trait CanSendTx: HasError {
    async fn send_tx(&self, messages: &[Any]) -> Result<Vec<Vec<Event>>, Self::Error>;
}

#[async_trait]
pub trait TxSender<Context>
where
    Context: HasError,
{
    async fn send_tx(
        context: &Context,
        messages: &[Any],
    ) -> Result<Vec<Vec<Event>>, Context::Error>;
}
