use async_trait::async_trait;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::event::split_events_by_messages;
use tendermint::abci::responses::Event;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::transaction::impls::estimate::CanEstimateTxFees;
use crate::transaction::impls::response::CanValidateRpcResponse;
use crate::transaction::impls::wait::{CanWaitTxHash, InjectWaitTxError};
use crate::transaction::traits::tx_sender::{CanSubmitTxWithFee, TxSender, TxSubmitter};

pub struct SimpleTxSender;

#[async_trait]
impl<Context> TxSubmitter<Context> for SimpleTxSender
where
    Context: InjectWaitTxError,
    Context: CanEstimateTxFees + CanSubmitTxWithFee + CanWaitTxHash + CanValidateRpcResponse,
{
    async fn submit_tx(context: &Context, messages: &[Any]) -> Result<Response, Context::Error> {
        let fee = context.estimate_tx_fees(messages).await?;

        let broadcast_response = context.submit_tx_with_fee(messages, &fee).await?;

        Context::validate_rpc_response_code(broadcast_response.code)?;

        Ok(broadcast_response)
    }
}

#[async_trait]
impl<Context> TxSender<Context> for SimpleTxSender
where
    Context: InjectWaitTxError,
    Context: CanWaitTxHash + CanValidateRpcResponse,
    Self: TxSubmitter<Context>,
{
    async fn send_tx(
        context: &Context,
        messages: &[Any],
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        let broadcast_response = Self::submit_tx(context, messages).await?;

        let deliver_response = context.wait_tx_hash(&broadcast_response.hash).await?;

        let events = split_events_by_messages(deliver_response.tx_result.events);

        Ok(events)
    }
}
