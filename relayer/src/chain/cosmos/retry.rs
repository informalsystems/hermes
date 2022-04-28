use core::future::Future;
use core::pin::Pin;
use core::time::Duration;
use ibc_proto::google::protobuf::Any;
use std::thread;
use tendermint::abci::Code;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::HttpClient;
use tonic::codegen::http::Uri;
use tracing::{debug, error, span, warn, Level};

use crate::chain::cosmos::query::account::refresh_account;
use crate::chain::cosmos::tx::estimate_fee_and_send_tx;
use crate::chain::cosmos::types::account::Account;
use crate::config::types::Memo;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::KeyEntry;
use crate::sdk_error::sdk_error_from_tx_sync_error_code;

// Maximum number of retries for send_tx in the case of
// an account sequence mismatch at broadcast step.
const MAX_ACCOUNT_SEQUENCE_RETRY: u64 = 1;

// Backoff multiplier to apply while retrying in the case
// of account sequence mismatch.
const BACKOFF_MULTIPLIER_ACCOUNT_SEQUENCE_RETRY: u64 = 300;

// The error "incorrect account sequence" is defined as the unique error code 32 in cosmos-sdk:
// https://github.com/cosmos/cosmos-sdk/blob/v0.44.0/types/errors/errors.go#L115-L117
const INCORRECT_ACCOUNT_SEQUENCE_ERR: u32 = 32;

/// Try to `send_tx` with retry on account sequence error.
/// An account sequence error can occur if the account sequence that
/// the relayer caches becomes outdated. This may happen if the relayer
/// wallet is used concurrently elsewhere, or when tx fees are mis-configured
/// leading to transactions hanging in the mempool.
///
/// Account sequence mismatch error can occur at two separate steps:
///   1. as Err variant, propagated from the `estimate_gas` step.
///   2. as an Ok variant, with an Code::Err response, propagated from
///     the `broadcast_tx_sync` step.
///
/// We treat both cases by re-fetching the account sequence number
/// from the full node.
/// Upon case #1, we do not retry submitting the same tx (retry happens
/// nonetheless at the worker `step` level). Upon case #2, we retry
/// submitting the same transaction.
pub async fn send_tx_with_account_sequence_retry(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    grpc_address: &Uri,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
    retry_counter: u64,
) -> Result<Response, Error> {
    crate::time!("send_tx_with_account_sequence_retry");
    let _span =
        span!(Level::ERROR, "send_tx_with_account_sequence_retry", id = %config.id).entered();

    do_send_tx_with_account_sequence_retry(
        config,
        rpc_client,
        grpc_address,
        key_entry,
        account,
        tx_memo,
        messages,
        retry_counter,
    )
    .await
}

// We have to do explicit return of `Box<dyn Future>` because Rust
// do not currently support recursive async functions behind the
// `async fn` syntactic sugar.
fn do_send_tx_with_account_sequence_retry<'a>(
    config: &'a ChainConfig,
    rpc_client: &'a HttpClient,
    grpc_address: &'a Uri,
    key_entry: &'a KeyEntry,
    account: &'a mut Account,
    tx_memo: &'a Memo,
    messages: Vec<Any>,
    retry_counter: u64,
) -> Pin<Box<dyn Future<Output = Result<Response, Error>> + 'a>> {
    Box::pin(async move {
        debug!(
            "sending {} messages using account sequence {}",
            messages.len(),
            account.sequence,
        );

        let tx_result = estimate_fee_and_send_tx(
            config,
            rpc_client,
            grpc_address,
            key_entry,
            account,
            tx_memo,
            messages.clone(),
        )
        .await;

        match tx_result {
            // Gas estimation failed with acct. s.n. mismatch at estimate gas step.
            // This indicates that the full node did not yet push the previous tx out of its
            // mempool. Possible explanations: fees too low, network congested, or full node
            // congested. Whichever the case, it is more expedient in production to drop the tx
            // and refresh the s.n., to allow proceeding to the other transactions. A separate
            // retry at the worker-level will handle retrying.
            Err(e) if mismatching_account_sequence_number(&e) => {
                warn!("failed at estimate_gas step mismatching account sequence: dropping the tx & refreshing account sequence number");
                refresh_account(grpc_address, &key_entry.account, account).await?;
                // Note: propagating error here can lead to bug & dropped packets:
                // https://github.com/informalsystems/ibc-rs/issues/1153
                // But periodic packet clearing will catch any dropped packets.
                Err(e)
            }

            // Gas estimation succeeded. Broadcasting failed with a retry-able error.
            Ok(response) if response.code == Code::Err(INCORRECT_ACCOUNT_SEQUENCE_ERR) => {
                if retry_counter < MAX_ACCOUNT_SEQUENCE_RETRY {
                    let retry_counter = retry_counter + 1;
                    warn!("failed at broadcast step with incorrect account sequence. retrying ({}/{})",
                        retry_counter, MAX_ACCOUNT_SEQUENCE_RETRY);
                    // Backoff & re-fetch the account s.n.
                    let backoff = retry_counter * BACKOFF_MULTIPLIER_ACCOUNT_SEQUENCE_RETRY;

                    thread::sleep(Duration::from_millis(backoff));
                    refresh_account(grpc_address, &key_entry.account, account).await?;

                    // Now retry.
                    do_send_tx_with_account_sequence_retry(
                        config,
                        rpc_client,
                        grpc_address,
                        key_entry,
                        account,
                        tx_memo,
                        messages,
                        retry_counter + 1,
                    )
                    .await
                } else {
                    // If after the max retry we still get an account sequence mismatch error,
                    // we ignore the error and return the original response to downstream.
                    // We do not return an error here, because the current convention
                    // let the caller handle error responses separately.
                    error!("failed due to account sequence errors. the relayer wallet may be used elsewhere concurrently.");
                    Ok(response)
                }
            }

            // Catch-all arm for the Ok variant.
            // This is the case when gas estimation succeeded.
            Ok(response) => {
                // Complete success.
                match response.code {
                    Code::Ok => {
                        debug!("broadcast_tx_sync: {:?}", response);

                        account.sequence.increment_mut();
                        Ok(response)
                    }
                    // Gas estimation succeeded, but broadcasting failed with unrecoverable error.
                    Code::Err(code) => {
                        // Avoid increasing the account s.n. if CheckTx failed
                        // Log the error
                        error!(
                            "broadcast_tx_sync: {:?}: diagnostic: {:?}",
                            response,
                            sdk_error_from_tx_sync_error_code(code)
                        );
                        Ok(response)
                    }
                }
            }

            // Catch-all case for the Err variant.
            // Gas estimation failure or other unrecoverable error, propagate.
            Err(e) => Err(e),
        }
    })
}

/// Determine whether the given error yielded by `tx_simulate`
/// indicates hat the current sequence number cached in Hermes
/// may be out-of-sync with the full node's version of the s.n.
fn mismatching_account_sequence_number(e: &Error) -> bool {
    use crate::error::ErrorDetail::*;

    match e.detail() {
        GrpcStatus(detail) => detail.is_account_sequence_mismatch(),
        _ => false,
    }
}
