use async_trait::async_trait;
use core::time::Duration;

use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::base::runtime::traits::time::{HasTime, Time};
use crate::base::transaction::traits::response::{CanQueryTxResponse, TxResponsePoller};
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub trait InjectNoTxResponseError: HasTxTypes {
    fn inject_tx_no_response_error(tx_hash: &Self::TxHash) -> Self::Error;
}

pub trait HasPollTimeout {
    fn poll_timeout(&self) -> Duration;

    fn poll_backoff(&self) -> Duration;
}

pub struct PollTxResponse;

#[async_trait]
impl<Context> TxResponsePoller<Context> for PollTxResponse
where
    Context: CanQueryTxResponse + HasPollTimeout + HasRuntime + InjectNoTxResponseError,
    Context::Runtime: HasTime + CanSleep,
{
    async fn poll_tx_response(
        context: &Context,
        tx_hash: &Context::TxHash,
    ) -> Result<Context::TxResponse, Context::Error> {
        let runtime = context.runtime();
        let wait_timeout = context.poll_timeout();
        let wait_backoff = context.poll_backoff();

        let start_time = runtime.now();

        loop {
            let response = context.query_tx_response(tx_hash).await?;

            match response {
                None => {
                    let elapsed = start_time.duration_since(&runtime.now());
                    if elapsed > wait_timeout {
                        return Err(Context::inject_tx_no_response_error(tx_hash));
                    } else {
                        runtime.sleep(wait_backoff).await;
                    }
                }
                Some(response) => {
                    return Ok(response);
                }
            }
        }
    }
}
