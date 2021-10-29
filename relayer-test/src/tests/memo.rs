use core::str::FromStr;
use eyre::eyre;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::config::{types::Memo, Config};
use serde_json as json;
use tracing::{debug, info};

use crate::bootstrap::channel::boostrap_chain_and_channel_pair;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::ibc::denom::derive_ibc_denom;
use crate::init::init_test;
use crate::util::random::{random_string, random_u64_range};

fn memo_config_modifier(memo: String) -> impl Fn(&mut Config) {
    move |config| {
        for mut chain in config.chains.iter_mut() {
            chain.memo_prefix = Memo::new(&memo);
        }
    }
}

#[test]
fn test_memo() -> Result<(), Error> {
    let test_config = init_test()?;
    let builder = ChainBuilder::new_with_config(&test_config);

    let memo = random_string();
    info!("testing IBC transfer with memo configured: \"{}\"", memo);

    let deployment = boostrap_chain_and_channel_pair(
        &builder,
        &PortId::from_str("transfer")?,
        memo_config_modifier(memo.clone()),
    )?;

    let denom_a = deployment.chains.side_a.denom();

    let a_to_b_amount = random_u64_range(1000, 5000);

    deployment.chains.side_a.chain_driver().transfer_token(
        &deployment.channel.port_a,
        &deployment.channel.channel_id_a,
        &deployment.chains.side_a.wallets().user1().address(),
        &deployment.chains.side_b.wallets().user1().address(),
        a_to_b_amount,
        &denom_a,
    )?;

    let denom_b = derive_ibc_denom(
        &deployment.channel.port_b.as_ref(),
        &deployment.channel.channel_id_b.as_ref(),
        &denom_a,
    )?;

    deployment
        .chains
        .side_b
        .chain_driver()
        .assert_eventual_wallet_amount(
            &deployment.chains.side_b.wallets().user1(),
            a_to_b_amount,
            &denom_b.as_ref(),
        )?;

    let tx_info = deployment
        .chains
        .side_b
        .chain_driver()
        .query_recipient_transactions(&deployment.chains.side_b.wallets().user1().address())?;

    assert_tx_memo_equals(&tx_info, &memo)?;

    Ok(())
}

fn assert_tx_memo_equals(tx_info: &json::Value, expected_memo: &str) -> Result<(), Error> {
    debug!("comparing memo field from json value {}", tx_info);

    let memo_field = &tx_info["txs"][0]["tx"]["body"]["memo"];

    debug!("memo field value: {}", memo_field);

    let memo_str = memo_field
        .as_str()
        .ok_or_else(|| eyre!("expect memo string field to be present in JSON"))?;

    assert_eq!(memo_str, expected_memo);

    Ok(())
}
