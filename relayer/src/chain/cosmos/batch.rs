use ibc_proto::google::protobuf::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{HttpClient, Url};
use tonic::codegen::http::Uri;
use tracing::{debug, error};

use crate::chain::cosmos::account::{AccountNumber, AccountSequence};
use crate::chain::cosmos::tx::estimate_fee_and_send_tx;
use crate::config::types::Memo;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::KeyEntry;
use crate::sdk_error::sdk_error_from_tx_sync_error_code;

// TODO: use this in send_messages_and_wait_commit
pub async fn send_messages_as_batches(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    grpc_address: &Uri,
    messages: Vec<Any>,
    account_sequence: &mut AccountSequence,
    account_number: AccountNumber,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Vec<Response>, Error> {
    let max_message_count = config.max_msg_num.0;
    let max_tx_size = config.max_tx_size.into();

    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let batches = batch_messages(messages, max_message_count, max_tx_size)?;

    let mut responses = Vec::new();

    for batch in batches {
        let response = estimate_fee_and_send_tx(
            config,
            rpc_client,
            rpc_address,
            grpc_address,
            batch,
            *account_sequence,
            account_number,
            key_entry,
            tx_memo,
        )
        .await?;

        maybe_update_account_sequence(config, account_sequence, &response);

        responses.push(response);
    }

    Ok(responses)
}

pub fn batch_messages(
    messages: Vec<Any>,
    max_message_count: usize,
    max_tx_size: usize,
) -> Result<Vec<Vec<Any>>, Error> {
    let mut batches = vec![];

    let mut current_count = 0;
    let mut current_size = 0;
    let mut current_batch = vec![];

    for message in messages.into_iter() {
        current_count += 1;
        current_size += message_size(&message)?;
        current_batch.push(message);

        if current_count >= max_message_count || current_size >= max_tx_size {
            let insert_batch = current_batch.drain(..).collect();
            batches.push(insert_batch);
            current_count = 0;
            current_size = 0;
        }
    }

    if !current_batch.is_empty() {
        batches.push(current_batch);
    }

    Ok(batches)
}

fn message_size(message: &Any) -> Result<usize, Error> {
    let mut buf = Vec::new();

    prost::Message::encode(message, &mut buf)
        .map_err(|e| Error::protobuf_encode("Message".into(), e))?;

    Ok(buf.len())
}

pub fn maybe_update_account_sequence(
    config: &ChainConfig,
    account_sequence: &mut AccountSequence,
    response: &Response,
) {
    match response.code {
        tendermint::abci::Code::Ok => {
            // A success means the account s.n. was increased
            account_sequence.increment_mut();
            debug!("[{}] send_tx: broadcast_tx_sync: {:?}", config.id, response);
        }
        tendermint::abci::Code::Err(code) => {
            // Avoid increasing the account s.n. if CheckTx failed
            // Log the error
            error!(
                "[{}] send_tx: broadcast_tx_sync: {:?}: diagnostic: {:?}",
                config.id,
                response,
                sdk_error_from_tx_sync_error_code(code)
            );
        }
    }
}
