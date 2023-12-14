use core::time::Duration;
use std::thread;

use ibc_proto::google::protobuf::Any;
use tendermint::abci::Code;
use tendermint_rpc::{
    endpoint::broadcast::tx_sync::Response,
    HttpClient,
};
use tracing::{
    debug,
    error,
    instrument,
    warn,
};

use crate::{
    chain::cosmos::{
        query::account::refresh_account,
        tx::estimate_fee_and_send_tx,
        types::{
            account::Account,
            config::TxConfig,
        },
    },
    config::types::Memo,
    error::Error,
    keyring::{
        Secp256k1KeyPair,
        SigningKeyPair,
    },
    sdk_error::sdk_error_from_tx_sync_error_code,
    telemetry,
    time,
};

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
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &mut Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    time!(
        "send_tx_with_account_sequence_retry",
        {
            "src_chain": config.chain_id,
        }
    );

    let _message_count = messages.len() as u64;

    let response = do_send_tx_with_account_sequence_retry(
        rpc_client, config, key_pair, account, tx_memo, messages,
    )
    .await;

    if response.is_ok() {
        telemetry!(messages_submitted, &config.chain_id, _message_count);
    }

    response
}

async fn do_send_tx_with_account_sequence_retry(
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &mut Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    match estimate_fee_and_send_tx(rpc_client, config, key_pair, account, tx_memo, messages).await {
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
                rpc_client, config, key_pair, account, tx_memo, messages,
            )
            .await
        }

        // Gas estimation succeeded but broadcast_tx_sync failed with a retry-able error.
        // NOTE: The error code could potentially overlap between Cosmos SDK and Ibc-go channel
        // error codes. This is currently not the case of incorrect account sequence error
        //which is the Cosmos SDK code 32 and Ibc-go channel errors only go up to 25.
        Ok(ref response) if response.code == Code::from(INCORRECT_ACCOUNT_SEQUENCE_ERR) => {
            warn!(
                ?response,
                "failed to broadcast tx because of a mismatched account sequence number, \
                refreshing account sequence number and retrying once"
            );

            telemetry!(
                broadcast_errors,
                &account.address.to_string(),
                response.code.into(),
                &response.log,
            );

            refresh_account_and_retry_send_tx_with_account_sequence(
                rpc_client, config, key_pair, account, tx_memo, messages,
            )
            .await
        }

        // Gas estimation succeeded and broadcast_tx_sync was either successful or has failed with
        // an unrecoverable error.
        Ok(response) => {
            debug!("gas estimation succeeded");

            // Gas estimation and broadcast_tx_sync were successful.
            // NOTE: The error code could potentially overlap between Cosmos SDK and Ibc-go channel
            // error codes.
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

                    telemetry!(
                        broadcast_errors,
                        &account.address.to_string(),
                        code.into(),
                        &response.log
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
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &mut Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    let key_account = key_pair.account();
    // Re-fetch the account sequence number
    refresh_account(&config.grpc_address, &key_account, account).await?;

    // Retry after delay
    thread::sleep(Duration::from_millis(ACCOUNT_SEQUENCE_RETRY_DELAY));

    estimate_fee_and_send_tx(rpc_client, config, key_pair, account, tx_memo, messages).await
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
