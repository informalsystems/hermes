use alloc::collections::btree_map::BTreeMap as HashMap;
use core::time::Duration;
use std::env;
use std::fs;
use std::sync::{Arc, RwLock};

use hermes_cosmos_integration_tests::contexts::binary_channel::setup::CosmosBinaryChannelSetup;
use hermes_cosmos_integration_tests::contexts::binary_channel::test_driver::CosmosBinaryChannelTestDriver;
use hermes_cosmos_integration_tests::contexts::bootstrap::CosmosBootstrap;
use hermes_cosmos_integration_tests::init::init_test_runtime;
use hermes_cosmos_relayer::contexts::build::CosmosBuilder;
use hermes_cosmos_test_components::chain::types::amount::Amount;
use hermes_error::types::Error;
use hermes_relayer_components::multi::types::index::Index;
use hermes_relayer_components::multi::types::index::Twindex;
use hermes_runtime_components::traits::runtime::HasRuntime;
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
use hermes_test_components::driver::traits::types::chain_driver_at::HasChainDriverAt;
use hermes_test_components::setup::traits::driver::CanBuildTestDriver;

use ibc_relayer::chain::cosmos::client::Settings;
use ibc_relayer::chain::handle::CountingAndCachingChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::registry::{Registry, SharedRegistry};
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::core::ics24_host::identifier::PortId;
use ibc_test_framework::bootstrap::binary::chain::save_relayer_config;
use ibc_test_framework::prelude::*;
use ibc_test_framework::prelude::{RelayerDriver, TestConfig};
use ibc_test_framework::util::random::random_u32;

#[test]
fn cosmos_integration_tests() -> Result<(), Error> {
    let runtime = init_test_runtime();

    let builder = Arc::new(CosmosBuilder::new_with_default(runtime.clone()));

    // TODO: load parameters from environment variables
    let bootstrap = Arc::new(CosmosBootstrap {
        runtime: runtime.clone(),
        builder,
        should_randomize_identifiers: true,
        chain_store_dir: "./test-data".into(),
        chain_command_path: "gaiad".into(),
        account_prefix: "cosmos".into(),
        staking_denom: "stake".into(),
        transfer_denom: "coin".into(),
        genesis_config_modifier: Box::new(|_| Ok(())),
        comet_config_modifier: Box::new(|_| Ok(())),
    });

    let create_client_settings = Settings {
        max_clock_drift: Duration::from_secs(40),
        trusting_period: None,
        trust_threshold: TrustThreshold::ONE_THIRD,
    };

    let setup = CosmosBinaryChannelSetup {
        bootstrap_a: bootstrap.clone(),
        bootstrap_b: bootstrap.clone(),
        create_client_settings,
        init_connection_options: Default::default(),
        init_channel_options: Default::default(),
        port_id: PortId::transfer(),
    };

    // TODO: Use a test suite entry point for running multiple tests
    runtime.runtime.clone().block_on(async move {
        let driver = setup.build_driver().await?;

        let chain_driver_a = driver.chain_driver_at(Index::<0>);
        let chain_driver_b = driver.chain_driver_at(Index::<1>);
        let chain_a = chain_driver_a.chain();
        let chain_b = chain_driver_b.chain();

        // Extract method `init_test()` but remove calls related to initialising tracing
        // as this would throw errors
        let mut test_config = {
            let chain_command_path =
                env::var("CHAIN_COMMAND_PATHS").unwrap_or_else(|_| "gaiad".to_string());

            let chain_command_paths = parse_chain_command_paths(chain_command_path);

            let base_chain_store_dir =
                env::var("CHAIN_STORE_DIR").unwrap_or_else(|_| "data".to_string());

            let account_prefix =
                env::var("ACCOUNT_PREFIXES").unwrap_or_else(|_| "cosmos".to_string());

            let native_token = env::var("NATIVE_TOKENS").unwrap_or_else(|_| "stake".to_string());

            let compat_modes = env::var("COMPAT_MODES").ok().map(parse_chain_command_paths);

            let ipv6_grpc = env::var("IPV6_GRPC")
                .ok()
                .map(|val| val == "true")
                .unwrap_or(false);

            let account_prefixes = parse_chain_command_paths(account_prefix);

            let native_tokens = parse_chain_command_paths(native_token);

            let chain_store_dir = format!("{}/test-{}", base_chain_store_dir, random_u32());

            fs::create_dir_all(&chain_store_dir)?;

            let chain_store_dir = fs::canonicalize(chain_store_dir)?;

            let hang_on_fail = env::var("HANG_ON_FAIL")
                .ok()
                .map(|val| val == "1")
                .unwrap_or(false);

            TestConfig {
                chain_command_paths,
                chain_store_dir,
                account_prefixes,
                hang_on_fail,
                bootstrap_with_random_ids: false,
                native_tokens,
                ipv6_grpc,
                compat_modes,
            }
        };

        test_config.chain_command_paths = vec![bootstrap
            .chain_command_path
            .clone()
            .to_string_lossy()
            .into()];
        test_config.chain_store_dir = bootstrap.chain_store_dir.clone();

        let config_path = test_config.chain_store_dir.join("relayer-config.toml");

        let mut config = Config::default();

        config
            .chains
            .push(ibc_relayer::config::ChainConfig::CosmosSdk(
                chain_a.chain_config.clone(),
            ));
        config
            .chains
            .push(ibc_relayer::config::ChainConfig::CosmosSdk(
                chain_b.chain_config.clone(),
            ));

        save_relayer_config(&config, &config_path)?;

        let registry: Registry<CountingAndCachingChainHandle> = Registry {
            config: config.clone(),
            handles: HashMap::new(),
            rt: chain_driver_a.runtime().runtime.clone(),
        };

        let shared_registry = SharedRegistry {
            registry: Arc::new(RwLock::new(registry)),
        };

        let relayer_v1_driver = RelayerDriver {
            config_path,
            config,
            registry: shared_registry,
            hang_on_fail: test_config.hang_on_fail,
        };

        test_ibc_transfer(&driver, relayer_v1_driver).await?;

        <Result<(), Error>>::Ok(())
    })?;

    Ok(())
}

fn parse_chain_command_paths(chain_command_path: String) -> Vec<String> {
    let patterns: Vec<String> = chain_command_path
        .split(',')
        .map(|chain_binary| chain_binary.to_string())
        .collect();
    patterns
}

pub async fn test_ibc_transfer(
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
