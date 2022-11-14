use async_trait::async_trait;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::event::split_events_by_messages;
use tendermint_rpc::abci::responses::Event;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::transaction::impls::broadcast::CanBroadcastTxSync;
use crate::transaction::impls::encode::CanSignTx;
use crate::transaction::impls::estimate::CanEstimateTxFees;
use crate::transaction::impls::response::CanValidateRpcResponse;
use crate::transaction::impls::wait::{CanWaitTxHash, InjectWaitTxError};
use crate::transaction::traits::fields::HasMaxFee;
use crate::transaction::traits::queries::account::CanQueryAccount;
use crate::transaction::traits::tx_sender::{TxSender, TxSubmitter};

pub struct SimpleTxSender;

#[async_trait]
impl<Context> TxSubmitter<Context> for SimpleTxSender
where
    Context: InjectWaitTxError,
    Context: CanQueryAccount
        + CanEstimateTxFees
        + CanValidateRpcResponse
        + CanSignTx
        + CanBroadcastTxSync
        + HasMaxFee,
{
    async fn submit_tx(context: &Context, messages: &[Any]) -> Result<Response, Context::Error> {
        let max_fee = context.max_fee();

        let account = context.query_account().await?;

        let simulate_tx = context
            .sign_tx(&max_fee, &account.sequence, messages)
            .await?;

        let fee = context.estimate_tx_fees(simulate_tx).await?;

        let tx = context.sign_tx(&fee, &account.sequence, messages).await?;

        let response = context.broadcast_tx_sync(tx).await?;

        Context::validate_rpc_response_code(response.code)?;

        Ok(response)
    }
}

#[async_trait]
impl<Context> TxSender<Context> for SimpleTxSender
where
    Context: InjectWaitTxError,
    Context: CanWaitTxHash,
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
