use core::time::Duration;
use ibc_proto::google::protobuf::Any;
use std::thread;
use tendermint::abci::Code;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tracing::{debug, error, span, warn, Level};

use crate::chain::cosmos::query::account::refresh_account;
use crate::chain::cosmos::tx::estimate_fee_and_send_tx;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::config::types::Memo;
use crate::error::Error;
use crate::keyring::KeyEntry;
use crate::sdk_error::sdk_error_from_tx_sync_error_code;
use crate::telemetry;

// Delay in milliseconds before retrying in the case of account sequence mismatch.
const ACCOUNT_SEQUENCE_RETRY_DELAY: u64 = 300;

// The error "incorrect account sequence" is defined as the unique error code 32 in cosmos-sdk:
// https://github.com/cosmos/cosmos-sdk/blob/v0.44.0/types/errors/errors.go#L115-L117
const INCORRECT_ACCOUNT_SEQUENCE_ERR: u32 = 32;

/// Try to `send_tx` and retry on account sequence error with re-cached account s.n.
/// An account sequence error can occur if the account sequence that
/// the relayer caches becomes outdated.
///
/// Account sequence mismatch error can occur at two separate steps:
///   1. as Err variant, propagated from the `estimate_gas` step.
///   2. as an Ok variant, with an Code::Err response, propagated from
///     the `broadcast_tx_sync` step.
///
/// We treat both cases by re-fetching the account sequence number
/// from the full node and retrying once with the new account s.n.
pub async fn send_tx_with_account_sequence_retry(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Response, Error> {
    crate::time!("send_tx_with_account_sequence_retry");

    let _span =
        span!(Level::ERROR, "send_tx_with_account_sequence_retry", id = %config.chain_id).entered();

    let _number_messages = messages.len() as u64;

    match do_send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, messages)
        .await
    {
        Ok(res) => {
            telemetry!(total_messages_submitted, &config.chain_id, _number_messages);
            Ok(res)
        }
        Err(e) => Err(e),
    }
}

async fn refresh_account_and_retry_send_tx_with_account_sequence(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Response, Error> {
    // Re-fetch the account s.n.
    refresh_account(&config.grpc_address, &key_entry.account, account).await?;
    // Retry after delay.
    thread::sleep(Duration::from_millis(ACCOUNT_SEQUENCE_RETRY_DELAY));
    estimate_fee_and_send_tx(config, key_entry, account, tx_memo, messages).await
}

async fn do_send_tx_with_account_sequence_retry(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Response, Error> {
    match estimate_fee_and_send_tx(config, key_entry, account, tx_memo, messages.clone()).await {
        // Gas estimation failed with acct. s.n. mismatch at estimate gas step.
        // It indicates that the account sequence cached by hermes is stale (got < expected).
        // This can happen when the same account is used by another agent.
        Err(ref e) if mismatch_account_sequence_number_error_requires_refresh(e) => {
            warn!(
                "failed at estimate_gas step mismatching account sequence {}. \
                refresh account sequence number and retry once",
                e
            );
            refresh_account_and_retry_send_tx_with_account_sequence(
                config, key_entry, account, tx_memo, messages,
            )
            .await
        }

        // Gas estimation succeeded but broadcast_tx_sync failed with a retry-able error.
        Ok(ref response) if response.code == Code::Err(INCORRECT_ACCOUNT_SEQUENCE_ERR) => {
            warn!(
                "failed at broadcast_tx_sync step with incorrect account sequence {:?}.  \
                refresh account sequence number and retry once",
                response
            );
            refresh_account_and_retry_send_tx_with_account_sequence(
                config, key_entry, account, tx_memo, messages,
            )
            .await
        }

        // Gas estimation succeeded and broadcast_tx_sync was either successful or has failed with
        // an unrecoverable error.
        Ok(response) => {
            // Gas estimation and broadcast_tx_sync were successful.
            match response.code {
                Code::Ok => {
                    // Increase account s.n.
                    debug!("broadcast_tx_sync: {:?}", response);
                    account.sequence.increment_mut();
                    Ok(response)
                }

                // Gas estimation succeeded, but broadcast_tx_sync failed with unrecoverable error.
                Code::Err(code) => {
                    // Do not increase the account s.n. since CheckTx step of broadcast_tx_sync has failed.
                    // Log the error.
                    error!(
                        "broadcast_tx_sync: {:?}: diagnostic: {:?}",
                        response,
                        sdk_error_from_tx_sync_error_code(code)
                    );
                    Ok(response)
                }
            }
        }

        // Gas estimation failure or other unrecoverable error, propagate.
        Err(e) => Err(e),
    }
}

/// Determine whether the given error yielded by `tx_simulate`
/// indicates that the current sequence number cached in Hermes
/// is smaller than the full node's version of the s.n. and therefore
/// account needs to be refreshed.
fn mismatch_account_sequence_number_error_requires_refresh(e: &Error) -> bool {
    use crate::error::ErrorDetail::*;

    match e.detail() {
        GrpcStatus(detail) => detail.is_account_sequence_mismatch_that_requires_refresh(),
        _ => false,
    }
}
