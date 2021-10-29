use core::str::FromStr;
use eyre::eyre;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use serde_json as json;
use tracing::info;

use crate::bootstrap::deployment::ChainDeployment;
use crate::bootstrap::pair::boostrap_chain_pair;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::ibc::denom::derive_ibc_denom;
use crate::init::init_test;
use crate::relayer::channel::{bootstrap_channel, Channel};
use crate::tagged::*;
use crate::util::random::random_u64_range;

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    let test_config = init_test()?;

    let builder = ChainBuilder::new_with_config(&test_config);

    let deployment = boostrap_chain_pair(&builder)?;

    let port = PortId::from_str("transfer")?;
    let port_a = DualTagged::new(port.clone());
    let port_b = DualTagged::new(port);

    let channel = bootstrap_channel(
        &deployment.client_b_to_a,
        &deployment.client_a_to_b,
        &port_a,
        &port_b,
    )?;

    info!("created new channel {:?}", channel);

    do_test_ibc_transfer(&deployment, &channel)?;

    // Test IBC transfer from the other direction from chain B to chain A

    let deployment = deployment.flip();
    let channel = channel.flip();

    do_test_ibc_transfer(&deployment, &channel)?;

    Ok(())
}

fn do_test_ibc_transfer<ChainA: ChainHandle, ChainB: ChainHandle>(
    deployment: &ChainDeployment<ChainA, ChainB>,
    channel: &Channel<ChainA, ChainB>,
) -> Result<(), Error> {
    let denom_a = deployment.side_a.denom();

    let chaina_user1_balance = deployment
        .side_a
        .chain_driver()
        .query_balance(&deployment.side_a.wallets().user1().address(), &denom_a)?;

    let a_to_b_amount = random_u64_range(1000, 5000);

    info!("Sending IBC transfer");

    deployment.side_a.chain_driver().transfer_token(
        &channel.port_a,
        &channel.channel_id_a,
        &deployment.side_a.wallets().user1().address(),
        &deployment.side_b.wallets().user1().address(),
        a_to_b_amount,
        &denom_a,
    )?;

    let denom_b = derive_ibc_denom(
        &channel.port_b.as_ref(),
        &channel.channel_id_b.as_ref(),
        &denom_a,
    )?;

    info!(
        "Waiting for user on chain B to receive transfer in denom {}",
        denom_b.value().0
    );

    deployment
        .side_a
        .chain_driver()
        .assert_eventual_wallet_amount(
            &deployment.side_a.wallets().user1(),
            chaina_user1_balance - a_to_b_amount,
            &denom_a,
        )?;

    deployment
        .side_b
        .chain_driver()
        .assert_eventual_wallet_amount(
            &deployment.side_b.wallets().user1(),
            a_to_b_amount,
            &denom_b.as_ref(),
        )?;

    let tx_info = deployment
        .side_b
        .chain_driver()
        .query_recipient_transactions(&deployment.side_b.wallets().user1().address())?;

    assert_tx_memo_equals(&tx_info, "testing memo")?;

    info!(
        "successfully performed IBC transfer from chain {} to chain {}",
        deployment.side_a.chain_id(),
        deployment.side_b.chain_id(),
    );

    let chaina_user2_balance = deployment
        .side_a
        .chain_driver()
        .query_balance(&deployment.side_a.wallets().user2().address(), &denom_a)?;

    let b_to_a_amount = random_u64_range(500, a_to_b_amount);

    deployment.side_b.chain_driver().transfer_token(
        &channel.port_b,
        &channel.channel_id_b,
        &deployment.side_b.wallets().user1().address(),
        &deployment.side_a.wallets().user2().address(),
        b_to_a_amount,
        &denom_b.as_ref(),
    )?;

    deployment
        .side_b
        .chain_driver()
        .assert_eventual_wallet_amount(
            &deployment.side_b.wallets().user1(),
            a_to_b_amount - b_to_a_amount,
            &denom_b.as_ref(),
        )?;

    deployment
        .side_a
        .chain_driver()
        .assert_eventual_wallet_amount(
            &deployment.side_a.wallets().user2(),
            chaina_user2_balance + b_to_a_amount,
            &denom_a,
        )?;

    info!(
        "successfully performed reverse IBC transfer from chain {} back to chain {}",
        deployment.side_b.chain_id(),
        deployment.side_a.chain_id(),
    );

    Ok(())
}

fn assert_tx_memo_equals(tx_info: &json::Value, expected_memo: &str) -> Result<(), Error> {
    info!("comparing memo field from json value {}", tx_info);

    let memo_field = &tx_info["txs"][0]["tx"]["body"]["memo"];

    info!("memo field value: {}", memo_field);

    let memo_str = memo_field
        .as_str()
        .ok_or_else(|| eyre!("expect memo string field to be present in JSON"))?;

    assert_eq!(memo_str, expected_memo);

    Ok(())
}
