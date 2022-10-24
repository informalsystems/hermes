use ibc_relayer_types::applications::ics29_fee::msgs::register_payee::build_register_counterparty_payee_message;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer_types::signer::Signer;

use crate::chain::cosmos::query::account::get_or_fetch_account;
use crate::chain::cosmos::query::fee::query_counterparty_payee;
use crate::chain::cosmos::retry::send_tx_with_account_sequence_retry;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::wait::wait_tx_succeed;
use crate::config::types::Memo;
use crate::error::Error;
use crate::keyring::KeyEntry;

pub async fn maybe_register_counterparty_payee(
    tx_config: &TxConfig,
    key_entry: &KeyEntry,
    m_account: &mut Option<Account>,
    tx_memo: &Memo,
    channel_id: &ChannelId,
    port_id: &PortId,
    address: &Signer,
    counterparty_payee: &Signer,
) -> Result<(), Error> {
    let account =
        get_or_fetch_account(&tx_config.grpc_address, &key_entry.account, m_account).await?;

    let current_counterparty_payee =
        query_counterparty_payee(&tx_config.grpc_address, channel_id, address).await?;

    match &current_counterparty_payee {
        Some(current_counterparty_payee)
            if current_counterparty_payee == counterparty_payee.as_ref() =>
        {
            Ok(())
        }
        _ => {
            let message = build_register_counterparty_payee_message(
                address,
                counterparty_payee,
                channel_id,
                port_id,
            )
            .map_err(Error::ics29)?;

            let response = send_tx_with_account_sequence_retry(
                tx_config,
                key_entry,
                account,
                tx_memo,
                &[message],
            )
            .await?;

            wait_tx_succeed(
                &tx_config.rpc_client,
                &tx_config.rpc_address,
                &tx_config.rpc_timeout,
                &response.hash,
            )
            .await?;

            Ok(())
        }
    }
}
