use core::mem;

use ibc::events::IbcEvent;
use ibc_proto::google::protobuf::Any;
use prost::Message;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::chain::cosmos::retry::send_tx_with_account_sequence_retry;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
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
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, batch).await?;

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
        let message_count = batch.len();

        let response =
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, batch).await?;

        if response.code.is_err() {
            let events_per_tx = vec![IbcEvent::ChainError(format!(
                "check_tx (broadcast_tx_sync) on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
                config.chain_id, response.hash, response.code, response.log
            )); message_count];

            let tx_sync_result = TxSyncResult {
                response,
                events: events_per_tx,
                status: TxStatus::ReceivedResponse,
            };

            tx_sync_results.push(tx_sync_result);
        } else {
            let tx_sync_result = TxSyncResult {
                response,
                events: Vec::new(),
                status: TxStatus::Pending { message_count },
            };

            tx_sync_results.push(tx_sync_result);
        }
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
        let message_len = message.encoded_len();

        if message_len > max_tx_size {
            return Err(Error::message_exceeds_max_tx_size(message_len));
        }

        if current_count >= max_message_count || current_size + message_len > max_tx_size {
            let insert_batch = mem::take(&mut current_batch);
            assert!(
                !insert_batch.is_empty(),
                "max message count should not be 0"
            );
            batches.push(insert_batch);
            current_count = 0;
            current_size = 0;
        }

        current_count += 1;
        current_size += message_len;
        current_batch.push(message);
    }

    if !current_batch.is_empty() {
        batches.push(current_batch);
    }

    Ok(batches)
}
