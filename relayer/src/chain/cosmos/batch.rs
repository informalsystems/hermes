use ibc::events::IbcEvent;
use ibc_proto::google::protobuf::Any;
use prost::Message;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::chain::cosmos::retry::send_tx_with_account_sequence_retry;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::types::tx::TxSyncResult;
use crate::chain::cosmos::wait::wait_for_block_commits;
use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
use crate::error::Error;
use crate::keyring::KeyEntry;

pub async fn send_batched_messages_and_wait_commit(
    config: &TxConfig,
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Vec<IbcEvent>, Error> {
    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let mut tx_sync_results = send_messages_as_batches(
        config,
        max_msg_num,
        max_tx_size,
        key_entry,
        account,
        tx_memo,
        messages,
    )
    .await?;

    wait_for_block_commits(
        &config.chain_id,
        &config.rpc_client,
        &config.rpc_address,
        &config.rpc_timeout,
        &mut tx_sync_results,
    )
    .await?;

    let events = tx_sync_results
        .into_iter()
        .flat_map(|el| el.events)
        .collect();

    Ok(events)
}

pub async fn send_batched_messages_and_wait_check_tx(
    config: &TxConfig,
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Vec<Response>, Error> {
    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let batches = batch_messages(max_msg_num, max_tx_size, messages)?;

    let mut responses = Vec::new();

    for batch in batches {
        let response =
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, batch, 0)
                .await?;

        responses.push(response);
    }

    Ok(responses)
}

async fn send_messages_as_batches(
    config: &TxConfig,
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Vec<TxSyncResult>, Error> {
    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let batches = batch_messages(max_msg_num, max_tx_size, messages)?;

    let mut tx_sync_results = Vec::new();

    for batch in batches {
        let events_per_tx = vec![IbcEvent::default(); batch.len()];

        let response =
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, batch, 0)
                .await?;

        let tx_sync_result = TxSyncResult {
            response,
            events: events_per_tx,
        };

        tx_sync_results.push(tx_sync_result);
    }

    Ok(tx_sync_results)
}

fn batch_messages(
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    messages: Vec<Any>,
) -> Result<Vec<Vec<Any>>, Error> {
    let max_message_count = max_msg_num.to_usize();
    let max_tx_size = max_tx_size.into();

    let mut batches = vec![];

    let mut current_count = 0;
    let mut current_size = 0;
    let mut current_batch = vec![];

    for message in messages.into_iter() {
        current_count += 1;
        current_size += message.encoded_len();
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
