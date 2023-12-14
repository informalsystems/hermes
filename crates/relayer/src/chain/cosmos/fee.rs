use ibc_relayer_types::{
    applications::ics29_fee::msgs::register_payee::build_register_counterparty_payee_message,
    core::ics24_host::identifier::{
        ChannelId,
        PortId,
    },
    signer::Signer,
};
use tendermint_rpc::HttpClient;

use crate::{
    chain::cosmos::{
        query::{
            account::get_or_fetch_account,
            fee::query_counterparty_payee,
        },
        retry::send_tx_with_account_sequence_retry,
        types::{
            account::Account,
            config::TxConfig,
        },
        wait::wait_tx_succeed,
    },
    config::types::Memo,
    error::Error,
    keyring::{
        Secp256k1KeyPair,
        SigningKeyPair,
    },
};

// FIXME: monster function, refactor
pub async fn maybe_register_counterparty_payee(
    rpc_client: &HttpClient,
    tx_config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    m_account: &mut Option<Account>,
    tx_memo: &Memo,
    channel_id: &ChannelId,
    port_id: &PortId,
    address: &Signer,
    counterparty_payee: &Signer,
) -> Result<(), Error> {
    let key_account = key_pair.account();
    let account = get_or_fetch_account(&tx_config.grpc_address, &key_account, m_account).await?;

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
                rpc_client,
                tx_config,
                key_pair,
                account,
                tx_memo,
                &[message],
            )
            .await?;

            wait_tx_succeed(
                rpc_client,
                &tx_config.rpc_address,
                &tx_config.rpc_timeout,
                &response.hash,
            )
            .await?;

            Ok(())
        }
    }
}
