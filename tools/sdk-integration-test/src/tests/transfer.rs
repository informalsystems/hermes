use hermes_cosmos_integration_tests::contexts::binary_channel::test_driver::CosmosBinaryChannelTestDriver;
use hermes_cosmos_test_components::chain::types::amount::Amount;
use hermes_error::types::Error;
use hermes_relayer_components::multi::types::index::Index;
use hermes_relayer_components::multi::types::index::Twindex;
use hermes_test_components::chain::traits::assert::eventual_amount::CanAssertEventualAmount;
use hermes_test_components::chain::traits::queries::balance::CanQueryBalance;
use hermes_test_components::chain::traits::transfer::amount::CanConvertIbcTransferredAmount;
use hermes_test_components::chain::traits::transfer::ibc_transfer::CanIbcTransferToken;
use hermes_test_components::chain::traits::types::amount::HasAmountMethods;
use hermes_test_components::chain_driver::traits::fields::amount::CanGenerateRandomAmount;
use hermes_test_components::chain_driver::traits::fields::denom_at::HasDenomAt;
use hermes_test_components::chain_driver::traits::fields::denom_at::TransferDenom;
use hermes_test_components::chain_driver::traits::types::chain::HasChain;
use hermes_test_components::driver::traits::channel_at::HasChannelAt;

use ibc_test_framework::prelude::RelayerDriver;
use ibc_test_framework::prelude::*;

use crate::tests::bootstrap::BoxFuture;

use super::bootstrap::bootstrap_and_run_test;

#[test]
fn run_test() -> Result<(), Error> {
    bootstrap_and_run_test::<_, BoxFuture<'_, Result<(), Error>>>(
        |setup, relay_driver| Box::pin(test_ibc_transfer(setup, relay_driver)),
        |_| Ok(()),
        |_| {},
        None,
        None,
    )
}

async fn test_ibc_transfer(
    setup: &CosmosBinaryChannelTestDriver,
    relay_driver: RelayerDriver,
) -> Result<(), Error> {
    let chain_driver_a = &setup.chain_driver_a;
    let chain_driver_b = &setup.chain_driver_b;

    let chain_a = chain_driver_a.chain();
    let chain_b = chain_driver_b.chain();

    let channel_id_a = setup.channel_id_at(Twindex::<0, 1>);
    let port_id_a = setup.port_id_at(Twindex::<0, 1>);

    let channel_id_b = setup.channel_id_at(Twindex::<1, 0>);
    let port_id_b = setup.port_id_at(Twindex::<1, 0>);

    // Missing native token for chains
    let denom_a = chain_driver_a.denom_at(TransferDenom, Index::<0>);

    let wallet_a = &chain_driver_a.user_wallet_a;
    let wallet_b = &chain_driver_b.user_wallet_a;
    let wallet_c = &chain_driver_a.user_wallet_b;

    let balance_a = chain_a.query_balance(&wallet_a.address, denom_a).await?;

    let a_to_b_amount = chain_driver_a.random_amount(1000, &balance_a).await;

    let expected_balance_a = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &balance_a,
        &a_to_b_amount,
    )?;
    let _handle = tokio::task::spawn_blocking(move || relay_driver.spawn_supervisor().unwrap());

    tokio::time::sleep(core::time::Duration::from_secs(10)).await;

    info!(
        "Sending IBC transfer from chain {} to chain {} with amount of {} {}",
        chain_a.chain_id, chain_b.chain_id, a_to_b_amount, denom_a
    );

    <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanIbcTransferToken<
        hermes_cosmos_relayer::contexts::chain::CosmosChain,
    >>::ibc_transfer_token(
        chain_a,
        channel_id_a,
        port_id_a,
        wallet_a,
        &wallet_b.address,
        &a_to_b_amount,
        &None,
    )
    .await?;

    info!(
        "Waiting for user on chain B to receive IBC transferred amount of {}",
        a_to_b_amount
    );
    tokio::time::sleep(core::time::Duration::from_secs(20)).await;

    chain_a
        .assert_eventual_amount(&wallet_a.address, &expected_balance_a)
        .await?;

    let expected_balance_b =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&a_to_b_amount, channel_id_b, port_id_b)?;

    chain_b
        .assert_eventual_amount(&wallet_b.address, &expected_balance_b)
        .await?;

    info!(
        "successfully performed IBC transfer from chain {} to chain {}",
        chain_a.chain_id, chain_b.chain_id,
    );

    let balance_c = chain_a.query_balance(&wallet_c.address, denom_a).await?;

    let b_to_a_amount = chain_driver_a
        .random_amount(1000, &expected_balance_b)
        .await;

    let expected_balance_b2 = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &expected_balance_b,
        &b_to_a_amount,
    )?;

    let b_to_a_amount_as_denom_a = Amount {
        quantity: b_to_a_amount.quantity,
        denom: denom_a.clone(),
    };

    let expected_balance_c = hermes_cosmos_relayer::contexts::chain::CosmosChain::add_amount(
        &balance_c,
        &b_to_a_amount_as_denom_a,
    )?;

    info!(
        "Sending IBC transfer from chain {} to chain {} with amount of {}",
        chain_b.chain_id, chain_a.chain_id, b_to_a_amount,
    );

    <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanIbcTransferToken<
        hermes_cosmos_relayer::contexts::chain::CosmosChain,
    >>::ibc_transfer_token(
        chain_b,
        channel_id_b,
        port_id_b,
        wallet_b,
        &wallet_c.address,
        &b_to_a_amount,
        &None,
    )
    .await?;

    chain_b
        .assert_eventual_amount(&wallet_b.address, &expected_balance_b2)
        .await?;

    chain_a
        .assert_eventual_amount(&wallet_c.address, &expected_balance_c)
        .await?;

    info!(
        "successfully performed reverse IBC transfer from chain {} back to chain {}",
        chain_b.chain_id, chain_a.chain_id,
    );

    Ok(())
}
