use ibc_proto::google::protobuf::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{HttpClient, Url};
use tonic::codegen::http::Uri;

use crate::chain::cosmos::retry::send_tx_with_account_sequence_retry;
use crate::chain::cosmos::types::account::Account;
use crate::config::types::Memo;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::KeyEntry;

// TODO: use this in send_messages_and_wait_commit
pub async fn send_messages_as_batches(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    grpc_address: &Uri,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
    account: &mut Account,
    messages: Vec<Any>,
) -> Result<Vec<Response>, Error> {
    let max_message_count = config.max_msg_num.0;
    let max_tx_size = config.max_tx_size.into();

    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let batches = batch_messages(messages, max_message_count, max_tx_size)?;

    let mut responses = Vec::new();

    for batch in batches {
        let response = send_tx_with_account_sequence_retry(
            config,
            rpc_client,
            rpc_address,
            grpc_address,
            key_entry,
            tx_memo,
            account,
            batch,
            0,
        )
        .await?;

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
