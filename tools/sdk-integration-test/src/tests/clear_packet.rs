use hermes_cosmos_integration_tests::contexts::binary_channel::test_driver::CosmosBinaryChannelTestDriver;
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

use crate::tests::bootstrap::bootstrap_and_run_test;
use crate::tests::bootstrap::BoxFuture;

#[test]
fn run_test() -> Result<(), Error> {
    bootstrap_and_run_test::<_, BoxFuture<'_, Result<(), Error>>>(
        |setup, relay_driver| Box::pin(test_clear_packet_no_scan(setup, relay_driver)),
        |_| Ok(()),
        |config| {
            // Disabling the client workers and clear_on_start should make the relayer not
            // relay any packet it missed before starting.
            config.mode.clients.enabled = false;
            config.mode.connections.enabled = false;
            config.mode.channels.enabled = false;

            config.mode.packets.enabled = true;
            config.mode.packets.clear_on_start = false;
            config.mode.packets.clear_interval = 10;
        },
        None,
        None,
    )
}

async fn test_clear_packet_no_scan(
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

    let denom_a = chain_driver_a.denom_at(TransferDenom, Index::<0>);
    // fee denom

    let wallet_a = &chain_driver_a.user_wallet_a;
    let wallet_b = &chain_driver_b.user_wallet_a;

    let balance_a = chain_a.query_balance(&wallet_a.address, denom_a).await?;

    let a_to_b_amount = chain_driver_a.random_amount(1000, &balance_a).await;

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

    tokio::time::sleep(Duration::from_secs(25)).await;

    let _handle = tokio::task::spawn_blocking(move || relay_driver.spawn_supervisor().unwrap());

    info!("Assert clear on start does not trigger");

    let expected_balance_a = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &balance_a,
        &a_to_b_amount,
    )?;

    let zero_coin = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &a_to_b_amount,
        &a_to_b_amount,
    )?;

    let expected_balance_b =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&zero_coin, channel_id_b, port_id_b)?;

    chain_a
        .assert_eventual_amount(&wallet_a.address, &expected_balance_a)
        .await?;

    chain_b
        .assert_eventual_amount(&wallet_b.address, &expected_balance_b)
        .await?;

    // Wait for clear interval to trigger
    tokio::time::sleep(Duration::from_secs(20)).await;

    info!("Assert clear interval does not trigger");

    chain_b
        .assert_eventual_amount(&wallet_b.address, &expected_balance_b)
        .await?;

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

    info!("Assert clear interval correctly triggers");

    let expected_balance_a2 = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &expected_balance_a,
        &a_to_b_amount,
    )?;

    let expected_balance_b2_as_coin =
        hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
            &a_to_b_amount,
            &a_to_b_amount,
        )?;

    let expected_balance_b2 =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&expected_balance_b2_as_coin, channel_id_b, port_id_b)?;

    chain_a
        .assert_eventual_amount(&wallet_a.address, &expected_balance_a2)
        .await?;

    info!("Assert clear interval does not trigger");

    chain_b
        .assert_eventual_amount(&wallet_b.address, &expected_balance_b2)
        .await?;

    Ok(())
}
