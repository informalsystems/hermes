use core::mem;

use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use prost::Message;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tracing::debug;

use crate::chain::cosmos::encode::encoded_tx_len;
use crate::chain::cosmos::gas::gas_amount_to_fee;
use crate::chain::cosmos::retry::send_tx_with_account_sequence_retry;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::cosmos::wait::wait_for_block_commits;
use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::keyring::KeyEntry;

/**
   Broadcast messages as multiple batched transactions to the chain all at once,
   and then wait for all transactions to be committed.
   This may improve performance in case when multiple transactions are
   committed into the same block. However this approach may not work if
   priority mempool is enabled.
*/
pub async fn send_batched_messages_and_wait_commit(
    config: &TxConfig,
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
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

/**
   Send batched messages one after another, only after the previous one
   has been committed. This is only used in case if parallel transactions
   are committed in the wrong order due to interference from priority mempool.
*/
pub async fn sequential_send_batched_messages_and_wait_commit(
    config: &TxConfig,
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    key_entry: &KeyEntry,
    account: &mut Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let tx_sync_results = sequential_send_messages_as_batches(
        config,
        max_msg_num,
        max_tx_size,
        key_entry,
        account,
        tx_memo,
        messages,
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

    let batches = batch_messages(
        config,
        max_msg_num,
        max_tx_size,
        key_entry,
        account,
        tx_memo,
        messages,
    )?;

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

    let message_count = messages.len();

    let batches = batch_messages(
        config,
        max_msg_num,
        max_tx_size,
        key_entry,
        account,
        tx_memo,
        messages,
    )?;

    debug!(
        "sending {} messages as {} batches to chain {} in parallel",
        message_count,
        batches.len(),
        config.chain_id
    );

    let mut tx_sync_results = Vec::new();

    for batch in batches {
        let message_count = batch.len();

        let response =
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, batch).await?;

        let tx_sync_result = response_to_tx_sync_result(&config.chain_id, message_count, response);

        tx_sync_results.push(tx_sync_result);
    }

    Ok(tx_sync_results)
}

async fn sequential_send_messages_as_batches(
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

    let message_count = messages.len();

    let batches = batch_messages(
        config,
        max_msg_num,
        max_tx_size,
        key_entry,
        account,
        tx_memo,
        messages,
    )?;

    debug!(
        "sending {} messages as {} batches to chain {} in serial",
        message_count,
        batches.len(),
        config.chain_id
    );

    let mut tx_sync_results = Vec::new();

    for batch in batches {
        let message_count = batch.len();

        let response =
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, batch).await?;

        let tx_sync_result = response_to_tx_sync_result(&config.chain_id, message_count, response);

        tx_sync_results.push(tx_sync_result);

        wait_for_block_commits(
            &config.chain_id,
            &config.rpc_client,
            &config.rpc_address,
            &config.rpc_timeout,
            &mut tx_sync_results,
        )
        .await?;
    }

    Ok(tx_sync_results)
}

fn response_to_tx_sync_result(
    chain_id: &ChainId,
    message_count: usize,
    response: Response,
) -> TxSyncResult {
    if response.code.is_err() {
        // Note: we don't have any height information in this case. This hack will fix itself
        // once we remove the `ChainError` event (which is not actually an event)
        let height = Height::new(chain_id.version(), 1).unwrap();

        let events_per_tx = vec![IbcEventWithHeight::new(IbcEvent::ChainError(format!(
            "check_tx (broadcast_tx_sync) on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
            chain_id, response.hash, response.code, response.log
        )), height); message_count];

        TxSyncResult {
            response,
            events: events_per_tx,
            status: TxStatus::ReceivedResponse,
        }
    } else {
        TxSyncResult {
            response,
            events: Vec::new(),
            status: TxStatus::Pending { message_count },
        }
    }
}

fn batch_messages(
    config: &TxConfig,
    max_msg_num: MaxMsgNum,
    max_tx_size: MaxTxSize,
    key_entry: &KeyEntry,
    account: &Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
) -> Result<Vec<Vec<Any>>, Error> {
    let max_message_count = max_msg_num.to_usize();
    let max_tx_size = max_tx_size.into();

    dbg!(config, key_entry, account, tx_memo);

    let mut batches = vec![];

    // Estimate the overhead of the transaction envelope's encoding,
    // by taking the encoded length of an empty tx with the same auth info and signatures.
    // Use the maximum possible fee to get an upper bound for varint encoding.
    let max_fee = gas_amount_to_fee(&config.gas_config, config.gas_config.max_gas);
    let tx_envelope_len = encoded_tx_len(config, key_entry, account, tx_memo, &[], &max_fee)?;

    let mut current_count = 0;
    let mut current_size = tx_envelope_len;
    let mut current_batch = vec![];

    for message in messages {
        let message_len = message.encoded_len();

        // The total length the message adds to the encoding includes the
        // field tag (small varint) and the length delimiter.
        let tagged_len = 1 + prost::length_delimiter_len(message_len) + message_len;

        if tx_envelope_len + tagged_len > max_tx_size {
            return Err(Error::message_too_big_for_tx(message_len));
        }

        if current_count >= max_message_count || current_size + tagged_len > max_tx_size {
            let insert_batch = mem::take(&mut current_batch);

            assert!(
                !insert_batch.is_empty(),
                "max message count should not be 0"
            );

            batches.push(insert_batch);
            current_count = 0;
            current_size = tx_envelope_len;
        }

        current_count += 1;
        current_size += tagged_len;
        current_batch.push(message);
    }

    if !current_batch.is_empty() {
        batches.push(current_batch);
    }

    Ok(batches)
}

#[cfg(test)]
mod tests {
    use super::batch_messages;
    use crate::chain::cosmos::test_utils::TestFixture;
    use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
    use ibc_proto::google::protobuf::Any;

    #[test]
    fn batch_does_not_exceed_max_tx_size() {
        let TestFixture {
            tx_config,
            key_entry,
            account,
        } = TestFixture::new();
        let messages = vec![
            Any {
                type_url: "/example.Foo".into(),
                value: vec![0; 6],
            },
            Any {
                type_url: "/example.Bar".into(),
                value: vec![0; 4],
            },
            Any {
                type_url: "/example.Baz".into(),
                value: vec![0; 2],
            },
        ];
        let batches = batch_messages(
            &tx_config,
            MaxMsgNum::default(),
            MaxTxSize::new(214).unwrap(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages,
        )
        .unwrap();

        assert_eq!(batches.len(), 2);
        assert_eq!(batches[0].len(), 2);
        assert_eq!(batches[0][0].type_url, "/example.Foo");
        assert_eq!(batches[0][0].value.len(), 6);
        assert_eq!(batches[0][1].type_url, "/example.Bar");
        assert_eq!(batches[0][1].value.len(), 4);

        assert_eq!(batches[1].len(), 1);
        assert_eq!(batches[1][0].type_url, "/example.Baz");
        assert_eq!(batches[1][0].value.len(), 2);
    }

    #[test]
    fn batch_error_on_oversized_message() {
        let TestFixture {
            tx_config,
            key_entry,
            account,
        } = TestFixture::new();
        let messages = vec![Any {
            type_url: "/example.Foo".into(),
            value: vec![0; 6],
        }];

        let batches = batch_messages(
            &tx_config,
            MaxMsgNum::default(),
            MaxTxSize::new(192).unwrap(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages.clone(),
        )
        .unwrap();

        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].len(), 1);

        let res = batch_messages(
            &tx_config,
            MaxMsgNum::default(),
            MaxTxSize::new(191).unwrap(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages,
        );

        assert!(res.is_err());
    }

    #[test]
    fn test_batches_are_structured_appropriately_per_max_msg_num() {
        let TestFixture {
            tx_config,
            key_entry,
            account,
        } = TestFixture::new();
        // Ensure that when MaxMsgNum is 1, the resulting batch
        // consists of 5 smaller batches, each with a single message
        let messages = vec![
            Any {
                type_url: "/example.Foo".into(),
                value: vec![0; 6],
            },
            Any {
                type_url: "/example.Bar".into(),
                value: vec![0; 4],
            },
            Any {
                type_url: "/example.Baz".into(),
                value: vec![0; 2],
            },
            Any {
                type_url: "/example.Bux".into(),
                value: vec![0; 3],
            },
            Any {
                type_url: "/example.Qux".into(),
                value: vec![0; 5],
            },
        ];

        let batches = batch_messages(
            &tx_config,
            MaxMsgNum::new(1).unwrap(),
            MaxTxSize::default(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages.clone(),
        )
        .unwrap();

        assert_eq!(batches.len(), 5);

        for batch in batches {
            assert_eq!(batch.len(), 1);
        }

        // Ensure that when MaxMsgNum > the number of messages, the resulting
        // batch consists of a single smaller batch with all of the messages
        let batches = batch_messages(
            &tx_config,
            MaxMsgNum::new(100).unwrap(),
            MaxTxSize::default(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages,
        )
        .unwrap();

        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].len(), 5);
    }

    #[test]
    fn test_batches_are_structured_appropriately_per_max_tx_size() {
        let TestFixture {
            tx_config,
            key_entry,
            account,
        } = TestFixture::new();
        // Ensure that when MaxTxSize is only enough to fit each one of the messages,
        // the resulting batch consists of 5 smaller batches, each with a single message.
        let messages = vec![
            Any {
                type_url: "/example.Foo".into(),
                value: vec![0; 10],
            },
            Any {
                type_url: "/example.Bar".into(),
                value: vec![0; 10],
            },
            Any {
                type_url: "/example.Baz".into(),
                value: vec![0; 10],
            },
            Any {
                type_url: "/example.Bux".into(),
                value: vec![0; 10],
            },
            Any {
                type_url: "/example.Qux".into(),
                value: vec![0; 10],
            },
        ];

        let batches = batch_messages(
            &tx_config,
            MaxMsgNum::default(),
            MaxTxSize::new(196).unwrap(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages.clone(),
        )
        .unwrap();

        assert_eq!(batches.len(), 5);

        for batch in batches {
            assert_eq!(batch.len(), 1);
        }

        // Ensure that when MaxTxSize > the size of all the messages, the
        // resulting batch consists of a single smaller batch with all of
        // messages inside
        let batches = batch_messages(
            &tx_config,
            MaxMsgNum::default(),
            MaxTxSize::max(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            messages,
        )
        .unwrap();

        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].len(), 5);
    }

    #[test]
    #[should_panic(expected = "`max_msg_num` must be greater than or equal to 1, found 0")]
    fn test_max_msg_num_of_zero_panics() {
        let TestFixture {
            tx_config,
            key_entry,
            account,
        } = TestFixture::new();
        let _batches = batch_messages(
            &tx_config,
            MaxMsgNum::new(0).unwrap(),
            MaxTxSize::default(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            vec![],
        );
    }
}
