use core::time::Duration;

use async_trait::async_trait;

use crate::logger::traits::level::HasBaseLogLevels;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::traits::sleep::CanSleep;
use crate::runtime::traits::time::HasTime;
use crate::std_prelude::*;
use crate::transaction::traits::logs::logger::CanLogTx;
use crate::transaction::traits::response::poll::TxResponsePoller;
use crate::transaction::traits::response::query::CanQueryTxResponse;
use crate::transaction::traits::types::HasTxTypes;

pub trait InjectNoTxResponseError: HasTxTypes {
    fn tx_no_response_error(tx_hash: &Self::TxHash) -> Self::Error;
}

pub trait HasPollTimeout {
    fn poll_timeout(&self) -> Duration;

    fn poll_backoff(&self) -> Duration;
}

pub struct PollTxResponse;

#[async_trait]
impl<Context> TxResponsePoller<Context> for PollTxResponse
where
    Context: CanLogTx + CanQueryTxResponse + HasPollTimeout + HasRuntime + InjectNoTxResponseError,
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
            let response = context.query_tx_response(tx_hash).await;

            match response {
                Ok(None) => {
                    let elapsed = Context::Runtime::duration_since(&start_time, &runtime.now());
                    if elapsed > wait_timeout {
                        context.log_tx(
                            Context::Logger::LEVEL_ERROR,
                            "no tx response received, and poll timeout has recached. returning error",
                            |log| {
                                log.debug("elapsed", &elapsed).debug("wait_timeout", &wait_timeout);
                            }
                        );

                        return Err(Context::tx_no_response_error(tx_hash));
                    } else {
                        runtime.sleep(wait_backoff).await;
                    }
                }
                Ok(Some(response)) => {
                    context.log_tx(
                        Context::Logger::LEVEL_TRACE,
                        "received tx response, finish polling",
                        |_| {},
                    );

                    return Ok(response);
                }
                Err(e) => {
                    context.log_tx(
                        Context::Logger::LEVEL_ERROR,
                        "query_tx_response returned error",
                        |log| {
                            log.debug("error", &e);
                        },
                    );

                    /*
                        If querying the TX response returns failure, it might be a temporary network
                        failure that can be recovered later on. Hence it would not be good if
                        we return error immediately, as we may still have the chance to get a
                        proper transaction response later on.

                        However, if the query still returns error after the wait timeout exceeded,
                        we return the error we get from the query.
                    */

                    let elapsed = Context::Runtime::duration_since(&start_time, &runtime.now());
                    if elapsed > wait_timeout {
                        return Err(e);
                    } else {
                        runtime.sleep(wait_backoff).await;
                    }
                }
            }
        }
    }
}
