use async_trait::async_trait;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasError;
use tendermint::abci::Event;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

#[async_trait]
pub trait CanSendTx: HasError {
    async fn send_tx_sync(&self, messages: &[Any]) -> Result<Vec<Vec<Event>>, Self::Error>;
}

#[async_trait]
pub trait CanSubmitTx: HasError {
    async fn submit_tx(&self, messages: &[Any]) -> Result<Response, Self::Error>;
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

#[async_trait]
pub trait TxSubmitter<Context>
where
    Context: HasError,
{
    async fn submit_tx(context: &Context, messages: &[Any]) -> Result<Response, Context::Error>;
}
