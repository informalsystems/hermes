use hermes_cosmos_chain_components::types::config::gas::dynamic_gas_config::DynamicGasConfig;
use hermes_cosmos_chain_components::types::config::gas::eip_type::EipQueryType;
use hermes_cosmos_integration_tests::contexts::binary_channel::test_driver::CosmosBinaryChannelTestDriver;
use hermes_error::types::Error;
use hermes_relayer_components::multi::types::index::Index;
use hermes_relayer_components::multi::types::index::Twindex;
use hermes_test_components::chain::traits::assert::eventual_amount::CanAssertEventualAmount;
use hermes_test_components::chain::traits::queries::balance::CanQueryBalance;
use hermes_test_components::chain::traits::transfer::amount::CanConvertIbcTransferredAmount;
use hermes_test_components::chain::traits::transfer::ibc_transfer::CanIbcTransferToken;
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

const DYNAMIC_GAS_MULTIPLIER: f64 = 1.2;
const DYNAMIC_GAS_MAX: f64 = 1.6;

#[test]
fn run_test() -> Result<(), Error> {
    bootstrap_and_run_test::<_, BoxFuture<'_, Result<(), Error>>>(
        |setup, relay_driver| Box::pin(test_dynamic_gas_fee(setup, relay_driver)),
        |genesis| {
            let maybe_params = genesis
                .get_mut("app_state")
                .and_then(|app_state| app_state.get_mut("feemarket"))
                .and_then(|feemarket| feemarket.get_mut("params"))
                .and_then(|params| params.as_object_mut());

            if let Some(params) = maybe_params {
                params
                    .insert(
                        "min_base_gas_price".to_owned(),
                        serde_json::Value::String("0.01".to_string()),
                    )
                    .ok_or_else(|| {
                        eyre!("failed to update feemarket `min_base_gas_price` in genesis file")
                    })?;
            }
            Ok(())
        },
        |config| {
            config.mode.clients.misbehaviour = false;
            config.mode.clients.refresh = false;
            config.mode.packets.clear_interval = 0;

            match &mut config.chains[0] {
                ChainConfig::CosmosSdk(chain_config_a) => {
                    chain_config_a.gas_price =
                        GasPrice::new(0.1, chain_config_a.gas_price.denom.clone());
                    chain_config_a.dynamic_gas_price =
                        DynamicGasPrice::unsafe_new(false, DYNAMIC_GAS_MULTIPLIER, DYNAMIC_GAS_MAX);
                }
            }

            match &mut config.chains[1] {
                ChainConfig::CosmosSdk(chain_config_b) => {
                    chain_config_b.gas_price =
                        GasPrice::new(0.1, chain_config_b.gas_price.denom.clone());
                    chain_config_b.dynamic_gas_price =
                        DynamicGasPrice::unsafe_new(true, DYNAMIC_GAS_MULTIPLIER, DYNAMIC_GAS_MAX);
                }
            }
        },
        None,
        Some(DynamicGasConfig {
            multiplier: DYNAMIC_GAS_MULTIPLIER,
            max: DYNAMIC_GAS_MAX,
            eip_query_type: EipQueryType::FeeMarket,
            denom: "stake".to_string(),
        }),
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

    let wallet_relayer_a = &chain_driver_a.relayer_wallet;
    let wallet_relayer_b = &chain_driver_b.relayer_wallet;

    let memo: String = MEMO_CHAR.repeat(MEMO_SIZE);

    let balance_a = chain_a.query_balance(&wallet_a.address, denom_a).await?;

    let a_to_b_amount = chain_driver_a.random_amount(1000, &balance_a).await;

    let gas_balance_a = chain_a
        .query_balance(&wallet_relayer_a.address, &gas_denom_b)
        .await?;

    let expected_balance_b =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&a_to_b_amount, channel_id_b, port_id_b)?;

    <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanIbcTransferToken<
        hermes_cosmos_relayer::contexts::chain::CosmosChain,
    >>::ibc_transfer_token(
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

    let gas_balance_a2 = chain_a
        .query_balance(&wallet_relayer_a.address, &gas_denom_a)
        .await?;

    let paid_fees_relayer_a = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &gas_balance_a,
        &gas_balance_a2,
    )?;

    // Stop supervisor
    drop(handle);

    let balance_b = chain_b.query_balance(&wallet_b.address, denom_b).await?;

    let b_to_a_amount = chain_driver_b.random_amount(1000, &balance_b).await;

    let expected_balance_a =
        <hermes_cosmos_relayer::contexts::chain::CosmosChain as CanConvertIbcTransferredAmount<
            hermes_cosmos_relayer::contexts::chain::CosmosChain,
        >>::ibc_transfer_amount_from(&b_to_a_amount, channel_id_a, port_id_a)?;

    let gas_balance_b = chain_b
        .query_balance(&wallet_relayer_b.address, &gas_denom_b)
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
        &None,
    )
    .await?;

    let _handle = tokio::task::spawn_blocking(move || relay_driver.spawn_supervisor().unwrap());

    chain_a
        .assert_eventual_amount(&wallet_a.address, &expected_balance_a)
        .await?;

    tokio::time::sleep(core::time::Duration::from_secs(5)).await;

    let gas_balance_b2 = chain_b
        .query_balance(&wallet_relayer_b.address, &gas_denom_b)
        .await?;

    let paid_fees_relayer_b = hermes_cosmos_relayer::contexts::chain::CosmosChain::subtract_amount(
        &gas_balance_b,
        &gas_balance_b2,
    )?;

    info!("paid gas fees for Tx with memo `{paid_fees_relayer_a}`, without memo `{paid_fees_relayer_b}`");

    assert!(
        paid_fees_relayer_a < paid_fees_relayer_b,
        "with dynamic gas enabled, gas paid for the first TX should be lower"
    );

    Ok(())
}
