use core::mem;

use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height;
use prost::Message;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tracing::debug;

use crate::chain::cosmos::encode::encoded_tx_metrics;
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
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, &batch)
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
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, &batch)
                .await?;

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
            send_tx_with_account_sequence_retry(config, key_entry, account, tx_memo, &batch)
                .await?;

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

    let mut batches = vec![];

    // Estimate the overhead of the transaction envelope's encoding,
    // by taking the encoded length of an empty tx with the same auth info and signatures.
    // Use the maximum possible fee to get an upper bound for varint encoding.
    let max_fee = gas_amount_to_fee(&config.gas_config, config.gas_config.max_gas);
    let tx_metrics = encoded_tx_metrics(config, key_entry, account, tx_memo, &[], &max_fee)?;
    let tx_envelope_len = tx_metrics.envelope_len;
    let empty_body_len = tx_metrics.body_bytes_len;

    // Full length of the transaction can then be derived from the length of the invariable
    // envelope and the length of the body field, taking into account the varint encoding
    // of the body field's length delimiter.
    fn tx_len(envelope_len: usize, body_len: usize) -> usize {
        // The caller has at least one message field length added to the body's
        debug_assert!(body_len != 0);
        envelope_len + 1 + prost::length_delimiter_len(body_len) + body_len
    }

    let mut current_count = 0;
    let mut current_len = empty_body_len;
    let mut current_batch = vec![];

    for message in messages {
        let message_len = message.encoded_len();

        // The total length the message adds to the encoding includes the
        // field tag (small varint) and the length delimiter.
        let tagged_len = 1 + prost::length_delimiter_len(message_len) + message_len;

        if current_count >= max_message_count
            || tx_len(tx_envelope_len, current_len + tagged_len) > max_tx_size
        {
            let insert_batch = mem::take(&mut current_batch);

            if insert_batch.is_empty() {
                assert!(max_message_count != 0);
                return Err(Error::message_too_big_for_tx(message_len));
            }

            batches.push(insert_batch);
            current_count = 0;
            current_len = empty_body_len;
        }

        current_count += 1;
        current_len += tagged_len;
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
    use crate::chain::cosmos::encode::sign_and_encode_tx;
    use crate::chain::cosmos::gas::gas_amount_to_fee;
    use crate::chain::cosmos::types::account::{
        Account, AccountAddress, AccountNumber, AccountSequence,
    };
    use crate::chain::cosmos::types::config::TxConfig;
    use crate::config;
    use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
    use crate::keyring::{self, KeyEntry, KeyRing};
    use ibc_proto::google::protobuf::Any;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;
    use std::fs;

    const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";

    fn test_fixture() -> (TxConfig, KeyEntry, Account) {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );
        let config = config::load(path).expect("could not parse config");
        let chain_id = ChainId::from_string("chain_A");
        let chain_config = config.find_chain(&chain_id).unwrap();

        let tx_config = TxConfig::try_from(chain_config).expect("could not obtain tx config");

        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer-seed.json"
        );
        let seed_file_content = fs::read_to_string(path).unwrap();
        let keyring = KeyRing::new(keyring::Store::Memory, "cosmos", &chain_id).unwrap();
        let hd_path = COSMOS_HD_PATH.parse().unwrap();
        let key_entry = keyring
            .key_from_seed_file(&seed_file_content, &hd_path)
            .unwrap();

        let account = Account {
            address: AccountAddress::new("".to_owned()),
            number: AccountNumber::new(0),
            sequence: AccountSequence::new(0),
        };

        (tx_config, key_entry, account)
    }

    #[test]
    fn batch_does_not_exceed_max_tx_size() {
        let (config, key_entry, account) = test_fixture();
        let max_fee = gas_amount_to_fee(&config.gas_config, config.gas_config.max_gas);
        let mut messages = vec![Any {
            type_url: "/example.Baz".into(),
            value: vec![0; 2],
        }];
        let memo = Memo::new("").unwrap();
        for n in 0..100 {
            messages.insert(
                messages.len() - 1,
                Any {
                    type_url: "/example.Foo".into(),
                    value: vec![0; n],
                },
            );
            let expected_batch_len = messages.len() - 1;
            let tx_bytes = sign_and_encode_tx(
                &config,
                &key_entry,
                &account,
                &memo,
                &messages[..expected_batch_len],
                &max_fee,
            )
            .unwrap();
            let max_tx_size = MaxTxSize::new(tx_bytes.len()).unwrap();

            let batches = batch_messages(
                &config,
                MaxMsgNum::new(100).unwrap(),
                max_tx_size,
                &key_entry,
                &account,
                &memo,
                messages.clone(),
            )
            .unwrap();

            assert_eq!(batches.len(), 2);
            assert_eq!(batches[0].len(), expected_batch_len);

            let tx_bytes =
                sign_and_encode_tx(&config, &key_entry, &account, &memo, &batches[0], &max_fee)
                    .unwrap();
            assert_eq!(tx_bytes.len(), max_tx_size.to_usize());

            assert_eq!(batches[1].len(), 1);
            assert_eq!(batches[1][0].type_url, "/example.Baz");
            assert_eq!(batches[1][0].value.len(), 2);
        }
    }

    #[test]
    fn batch_error_on_oversized_message() {
        const MAX_TX_SIZE: usize = 203;

        let (config, key_entry, account) = test_fixture();
        let messages = vec![Any {
            type_url: "/example.Foo".into(),
            value: vec![0; 6],
        }];
        let memo = Memo::new("example").unwrap();

        let batches = batch_messages(
            &config,
            MaxMsgNum::default(),
            MaxTxSize::new(MAX_TX_SIZE).unwrap(),
            &key_entry,
            &account,
            &memo,
            messages.clone(),
        )
        .unwrap();

        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].len(), 1);

        let max_fee = gas_amount_to_fee(&config.gas_config, config.gas_config.max_gas);
        let tx_bytes =
            sign_and_encode_tx(&config, &key_entry, &account, &memo, &batches[0], &max_fee)
                .unwrap();
        assert_eq!(tx_bytes.len(), MAX_TX_SIZE);

        let res = batch_messages(
            &config,
            MaxMsgNum::default(),
            MaxTxSize::new(MAX_TX_SIZE - 1).unwrap(),
            &key_entry,
            &account,
            &memo,
            messages,
        );

        assert!(res.is_err());
    }

    #[test]
    fn test_batches_are_structured_appropriately_per_max_msg_num() {
        let (config, key_entry, account) = test_fixture();
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
            &config,
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
            &config,
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
        const MAX_TX_SIZE: usize = 198;

        let (config, key_entry, account) = test_fixture();
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
        let memo = Memo::new("").unwrap();

        let batches = batch_messages(
            &config,
            MaxMsgNum::default(),
            MaxTxSize::new(MAX_TX_SIZE).unwrap(),
            &key_entry,
            &account,
            &memo,
            messages.clone(),
        )
        .unwrap();

        assert_eq!(batches.len(), 5);

        let max_fee = gas_amount_to_fee(&config.gas_config, config.gas_config.max_gas);

        for batch in batches {
            assert_eq!(batch.len(), 1);
            let tx_bytes =
                sign_and_encode_tx(&config, &key_entry, &account, &memo, &batch, &max_fee).unwrap();
            assert_eq!(tx_bytes.len(), MAX_TX_SIZE);
        }

        // Ensure that when MaxTxSize > the size of all the messages, the
        // resulting batch consists of a single smaller batch with all of
        // messages inside
        let batches = batch_messages(
            &config,
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
        let (config, key_entry, account) = test_fixture();
        let _batches = batch_messages(
            &config,
            MaxMsgNum::new(0).unwrap(),
            MaxTxSize::default(),
            &key_entry,
            &account,
            &Memo::new("").unwrap(),
            vec![],
        );
    }
}
