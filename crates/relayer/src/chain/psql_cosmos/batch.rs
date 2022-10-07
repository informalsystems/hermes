use sqlx::PgPool;

use ibc_proto::google::protobuf::Any;

use crate::chain::cosmos::batch::send_messages_as_batches;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::psql_cosmos::wait::wait_for_block_commits;
use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::keyring::KeyEntry;

#[allow(clippy::too_many_arguments)]
pub async fn send_batched_messages_and_wait_commit(
    pool: &PgPool,
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

    wait_for_block_commits(pool, config, &mut tx_sync_results).await?;

    let events = tx_sync_results
        .into_iter()
        .flat_map(|el| el.events)
        .collect();

    Ok(events)
}
