use hermes_cosmos_integration_tests::contexts::binary_channel::test_driver::CosmosBinaryChannelTestDriver;
use hermes_error::types::Error;
use hermes_relayer_components::multi::types::index::Index;
use hermes_relayer_components::multi::types::index::Twindex;
use hermes_test_components::chain::traits::assert::eventual_amount::CanAssertEventualAmount;
use hermes_test_components::chain::traits::queries::balance::CanQueryBalance;
use hermes_test_components::chain::traits::transfer::amount::CanConvertIbcTransferredAmount;
use hermes_test_components::chain::traits::transfer::ibc_transfer::CanIbcTransferToken;
use hermes_test_components::chain::traits::transfer::ibc_transfer::CanIbcTransferTokenWithMemo;
use hermes_test_components::chain::traits::types::amount::HasAmountMethods;
use hermes_test_components::chain::traits::types::denom::DenomOf;
use hermes_test_components::chain_driver::traits::fields::amount::CanGenerateRandomAmount;
use hermes_test_components::chain_driver::traits::fields::denom_at::HasDenomAt;
use hermes_test_components::chain_driver::traits::fields::denom_at::TransferDenom;
use hermes_test_components::chain_driver::traits::types::chain::HasChain;
use hermes_test_components::driver::traits::channel_at::HasChannelAt;

use ibc_relayer::config::dynamic_gas::DynamicGasPrice;
use ibc_relayer::config::ChainConfig;
use ibc_relayer::config::GasPrice;
use ibc_test_framework::prelude::RelayerDriver;
use ibc_test_framework::prelude::*;

use crate::tests::bootstrap::BoxFuture;

use super::bootstrap::bootstrap_and_run_test;

const MEMO_CHAR: &str = "a";
const MEMO_SIZE: usize = 10000;

// Disabled until this is fixed: https://github.com/informalsystems/hermes-sdk/blob/main/crates/cosmos/cosmos-test-components/src/bootstrap/impls/initializers/update_genesis_config.rs#L76
//#[test]
fn run_test() -> Result<(), Error> {
    bootstrap_and_run_test::<_, BoxFuture<'_, Result<(), Error>>>(
        |setup, relay_driver| Box::pin(test_dynamic_gas_fee(setup, relay_driver)),
        |config| {
            config.mode.clients.misbehaviour = false;
            config.mode.clients.refresh = false;
            config.mode.packets.clear_interval = 0;

            match &mut config.chains[0] {
                ChainConfig::CosmosSdk(chain_config_a) => {
                    chain_config_a.gas_price =
                        GasPrice::new(0.1, chain_config_a.gas_price.denom.clone());
                    chain_config_a.dynamic_gas_price = DynamicGasPrice::unsafe_new(false, 1.1, 1.6);
                }
            }

            match &mut config.chains[1] {
                ChainConfig::CosmosSdk(chain_config_b) => {
                    chain_config_b.gas_price =
                        GasPrice::new(0.1, chain_config_b.gas_price.denom.clone());
                    chain_config_b.dynamic_gas_price = DynamicGasPrice::unsafe_new(true, 1.1, 1.6);
                }
            }
        },
    )
}

async fn test_dynamic_gas_fee(
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
    let denom_b = chain_driver_b.denom_at(TransferDenom, Index::<0>);

    let gas_denom_a = <DenomOf<hermes_cosmos_relayer::contexts::chain::CosmosChain>>::base("stake");
    let gas_denom_b = <DenomOf<hermes_cosmos_relayer::contexts::chain::CosmosChain>>::base("stake");

    let wallet_a = &chain_driver_a.user_wallet_a;
    let wallet_b = &chain_driver_b.user_wallet_a;

    let memo: String = MEMO_CHAR.repeat(MEMO_SIZE);

    let balance_a = chain_a.query_balance(&wallet_a.address, denom_a).await?;

    let a_to_b_amount = chain_driver_a.random_amount(1000, &balance_a).await;

    let gas_balance_b = chain_a
        .query_balance(&wallet_a.address, &gas_denom_b)
        .await?;

    let expected_balance_b =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&a_to_b_amount, channel_id_b, port_id_b)?;

    // TODO: Missing transfer with memo
    <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanIbcTransferTokenWithMemo<
        hermes_cosmos_relayer::contexts::chain::CosmosChain,
    >>::ibc_transfer_token_with_memo(
        chain_a,
        channel_id_a,
        port_id_a,
        wallet_a,
        &wallet_b.address,
        &a_to_b_amount,
        &Some(memo),
    )
    .await?;

    let cloned_relay_driver = relay_driver.clone();

    let handle =
        tokio::task::spawn_blocking(move || cloned_relay_driver.spawn_supervisor().unwrap());

    chain_b
        .assert_eventual_amount(&wallet_b.address, &expected_balance_b)
        .await?;

    tokio::time::sleep(core::time::Duration::from_secs(5)).await;

    let gas_balance_b2 = chain_a
        .query_balance(&wallet_a.address, &gas_denom_b)
        .await?;

    let paid_fees_relayer_b = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &gas_balance_b,
        &gas_balance_b2,
    )?;

    // Stop supervisor
    drop(handle);

    let balance_b = chain_a.query_balance(&wallet_b.address, denom_b).await?;
    let b_to_a_amount = chain_driver_a.random_amount(1000, &balance_b).await;

    let expected_balance_a =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&b_to_a_amount, channel_id_a, port_id_a)?;

    let gas_balance_a = chain_a
        .query_balance(&wallet_a.address, &gas_denom_a)
        .await?;

    <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanIbcTransferToken<
        hermes_cosmos_relayer::contexts::chain::CosmosChain,
    >>::ibc_transfer_token(
        chain_b,
        channel_id_b,
        port_id_b,
        wallet_b,
        &wallet_a.address,
        &b_to_a_amount,
    )
    .await?;

    let _handle = tokio::task::spawn_blocking(move || relay_driver.spawn_supervisor().unwrap());

    chain_a
        .assert_eventual_amount(&wallet_a.address, &expected_balance_a)
        .await?;

    tokio::time::sleep(core::time::Duration::from_secs(5)).await;

    let gas_balance_a2 = chain_a
        .query_balance(&wallet_a.address, &gas_denom_b)
        .await?;

    let paid_fees_relayer_a = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &gas_balance_a,
        &gas_balance_a2,
    )?;

    info!("paid gas fees for Tx with memo `{paid_fees_relayer_b}`, without memo `{paid_fees_relayer_a}`");

    assert!(
        paid_fees_relayer_b < paid_fees_relayer_a,
        "with dynamic gas enabled, gas paid for the first TX should be lower"
    );

    Ok(())
}
