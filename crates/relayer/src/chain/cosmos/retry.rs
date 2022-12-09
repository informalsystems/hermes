use core::time::Duration;
use std::thread;

use tracing::{debug, error, instrument, warn};

use ibc_proto::google::protobuf::Any;
use tendermint::abci::Code;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::chain::cosmos::query::account::refresh_account;
use crate::chain::cosmos::tx::estimate_fee_and_send_tx;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::config::types::Memo;
use crate::error::Error;
use crate::keyring::KeyEntry;
use crate::sdk_error::sdk_error_from_tx_sync_error_code;
use crate::{telemetry, time};

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
#[instrument(
    name = "send_tx_with_account_sequence_retry",
    level = "error",
    skip_all,
    fields(
        chain = %config.chain_id,
        account.sequence = %account.sequence,
    ),
)]
pub async fn send_tx_with_account_sequence_retry(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    time!("send_tx_with_account_sequence_retry");

    let _message_count = messages.len() as u64;

    let response =
        do_send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, messages).await;

    if response.is_ok() {
        telemetry!(total_messages_submitted, &config.chain_id, _message_count);
    }

    response
}

async fn do_send_tx_with_account_sequence_retry(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    match estimate_fee_and_send_tx(config, key_entry, account, tx_memo, messages).await {
        // Gas estimation failed with account sequence mismatch during gas estimation.
        // It indicates that the account sequence cached by hermes is stale (got < expected).
        // This can happen when the same account is used by another agent.
        Err(ref e) if mismatch_account_sequence_number_error_requires_refresh(e) => {
            warn!(
                error = %e,
                "failed to estimate gas because of a mismatched account sequence number, \
                refreshing account sequence number and retrying once",
            );

            refresh_account_and_retry_send_tx_with_account_sequence(
                config, key_entry, account, tx_memo, messages,
            )
            .await
        }

        // Gas estimation succeeded but broadcast_tx_sync failed with a retry-able error.
        Ok(ref response) if response.code == Code::from(INCORRECT_ACCOUNT_SEQUENCE_ERR) => {
            warn!(
                ?response,
                "failed to broadcast tx because of a mismatched account sequence number, \
                refreshing account sequence number and retrying once"
            );

            refresh_account_and_retry_send_tx_with_account_sequence(
                config, key_entry, account, tx_memo, messages,
            )
            .await
        }

        // Gas estimation succeeded and broadcast_tx_sync was either successful or has failed with
        // an unrecoverable error.
        Ok(response) => {
            debug!("gas estimation succeeded");

            // Gas estimation and broadcast_tx_sync were successful.
            match response.code {
                Code::Ok => {
                    let old_account_sequence = account.sequence;

                    // Increase account s.n.
                    account.sequence.increment_mut();

                    debug!(
                        ?response,
                        account.sequence.old = %old_account_sequence,
                        account.sequence.new = %account.sequence,
                        "tx was successfully broadcasted, \
                        increasing account sequence number"
                    );

                    Ok(response)
                }

                // Gas estimation succeeded, but broadcast_tx_sync failed with unrecoverable error.
                Code::Err(code) => {
                    // Do not increase the account s.n. since CheckTx step of broadcast_tx_sync has failed.
                    // Log the error.
                    error!(
                        ?response,
                        diagnostic = ?sdk_error_from_tx_sync_error_code(code.into()),
                        "failed to broadcast tx with unrecoverable error"
                    );

                    Ok(response)
                }
            }
        }

        // Gas estimation failure or other unrecoverable error, propagate.
        Err(e) => {
            error!(error = %e, "gas estimation failed or encountered another unrecoverable error");

            Err(e)
        }
    }
}

async fn refresh_account_and_retry_send_tx_with_account_sequence(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    // Re-fetch the account sequence number
    refresh_account(&config.grpc_address, &key_entry.account, account).await?;

    // Retry after delay
    thread::sleep(Duration::from_millis(ACCOUNT_SEQUENCE_RETRY_DELAY));

    estimate_fee_and_send_tx(config, key_entry, account, tx_memo, messages).await
}

/// Determine whether the given error yielded by `tx_simulate`
/// indicates that the current account sequence number cached in Hermes
/// is smaller than the full node's version of the sequence number and therefore
/// the account needs to be refreshed.
fn mismatch_account_sequence_number_error_requires_refresh(e: &Error) -> bool {
    use crate::error::ErrorDetail::*;

    match e.detail() {
        GrpcStatus(detail) => detail.is_account_sequence_mismatch_that_requires_refresh(),
        _ => false,
    }
}
