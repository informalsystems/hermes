use async_trait::async_trait;
use ibc_relayer_framework::base::core::traits::error::HasError;
use std::time::Instant;
use tendermint_rpc::abci::transaction::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tokio::time::sleep;

use crate::transaction::impls::queries::tx::CanQueryTxResponse;
use crate::transaction::impls::response::CanValidateRpcResponse;
use crate::transaction::traits::fields::HasWaitTimeout;

#[async_trait]
pub trait CanWaitTxHash: HasError {
    async fn wait_tx_hash(&self, tx_hash: &TxHash) -> Result<TxResponse, Self::Error>;
}

#[async_trait]
pub trait TxHashWaiter<Context>
where
    Context: HasError,
{
    async fn wait_tx_hash(
        context: &Context,
        tx_hash: &TxHash,
    ) -> Result<TxResponse, Context::Error>;
}

pub trait InjectWaitTxError: HasError {
    fn tx_no_confirmation_error() -> Self::Error;
}

pub struct BaseWaitTxHash;

pub struct WaitTxSucceed;

#[async_trait]
impl<Context> TxHashWaiter<Context> for WaitTxSucceed
where
    Context: InjectWaitTxError,
    Context: HasWaitTimeout,
    Context: CanQueryTxResponse + CanValidateRpcResponse,
    BaseWaitTxHash: TxHashWaiter<Context>,
{
    async fn wait_tx_hash(
        context: &Context,
        tx_hash: &TxHash,
    ) -> Result<TxResponse, Context::Error> {
        let response = BaseWaitTxHash::wait_tx_hash(context, tx_hash).await?;

        Context::validate_rpc_response_code(response.tx_result.code)?;

        Ok(response)
    }
}

#[async_trait]
impl<Context> TxHashWaiter<Context> for BaseWaitTxHash
where
    Context: InjectWaitTxError,
    Context: HasWaitTimeout,
    Context: CanQueryTxResponse,
{
    async fn wait_tx_hash(
        context: &Context,
        tx_hash: &TxHash,
    ) -> Result<TxResponse, Context::Error> {
        let wait_timeout = context.wait_timeout();
        let wait_backoff = context.wait_backoff();

        let start_time = Instant::now();

        loop {
            let response = context.query_tx_response(tx_hash).await?;

            match response {
                None => {
                    let elapsed = start_time.elapsed();
                    if &elapsed > wait_timeout {
                        return Err(Context::tx_no_confirmation_error());
                    } else {
                        sleep(*wait_backoff).await;
                    }
                }
                Some(response) => {
                    return Ok(response);
                }
            }
        }
    }
}
