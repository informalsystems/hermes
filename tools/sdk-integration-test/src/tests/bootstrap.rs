use alloc::collections::btree_map::BTreeMap as HashMap;
use core::time::Duration;
use hermes_cosmos_chain_components::types::config::gas::dynamic_gas_config::DynamicGasConfig;
use hermes_cosmos_integration_tests::contexts::binary_channel::test_driver::CosmosBinaryChannelTestDriver;
use serde_json::Value as JsonValue;
use std::env;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, RwLock};

use hermes_cosmos_integration_tests::contexts::binary_channel::setup::CosmosBinaryChannelSetup;
use hermes_cosmos_integration_tests::contexts::bootstrap::CosmosBootstrap;
use hermes_cosmos_integration_tests::init::init_test_runtime;
use hermes_cosmos_relayer::contexts::build::CosmosBuilder;
use hermes_error::types::Error;
use hermes_relayer_components::multi::types::index::Index;
use hermes_runtime_components::traits::runtime::HasRuntime;
use hermes_test_components::chain_driver::traits::types::chain::HasChain;
use hermes_test_components::driver::traits::types::chain_driver_at::HasChainDriverAt;
use hermes_test_components::setup::traits::driver::CanBuildTestDriver;

use ibc_relayer::chain::cosmos::client::Settings;
use ibc_relayer::chain::handle::CountingAndCachingChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::registry::{Registry, SharedRegistry};
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::core::ics24_host::identifier::PortId;
use ibc_test_framework::bootstrap::binary::chain::save_relayer_config;
use ibc_test_framework::prelude::{RelayerDriver, TestConfig};

pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

#[allow(clippy::type_complexity)]
pub fn bootstrap_and_run_test<F, Fut>(
    test_method: F,
    genesis_modifier: impl Fn(&mut JsonValue) -> Result<(), Error> + Send + Sync + 'static,
    config_modifier: impl FnOnce(&mut Config),
    dynamic_gas_config1: Option<DynamicGasConfig>,
    dynamic_gas_config2: Option<DynamicGasConfig>,
) -> Result<(), Error>
where
    F: for<'a> Fn(
            &'a CosmosBinaryChannelTestDriver,
            RelayerDriver,
        ) -> BoxFuture<'a, Result<(), Error>>
        + Send
        + Sync
        + 'static,
{
    let runtime = init_test_runtime();

    let builder = Arc::new(CosmosBuilder::new_with_default(runtime.clone()));

    let chain_command_path =
        env::var("CHAIN_COMMAND_PATHS").unwrap_or_else(|_| "gaiad".to_string());
    let chain_command_paths: Vec<String> = parse_chain_command_paths(chain_command_path);

    let account_prefix = env::var("ACCOUNT_PREFIXES").unwrap_or_else(|_| "cosmos".to_string());
    let account_prefixes = parse_chain_command_paths(account_prefix);

    let native_token = env::var("NATIVE_TOKENS").unwrap_or_else(|_| "stake".to_string());
    let native_tokens = parse_chain_command_paths(native_token);

    // TODO: load parameters from environment variables
    let bootstrap1 = Arc::new(CosmosBootstrap {
        runtime: runtime.clone(),
        cosmos_builder: builder.clone(),
        should_randomize_identifiers: true,
        chain_store_dir: "./test-data".into(),
        chain_command_path: chain_command_paths[0 % chain_command_paths.len()]
            .as_str()
            .into(),
        account_prefix: account_prefixes[0 % account_prefixes.len()].as_str().into(),
        staking_denom_prefix: native_tokens[0 % native_tokens.len()].as_str().into(),
        transfer_denom_prefix: "coin".into(),
        genesis_config_modifier: Box::new(genesis_modifier),
        comet_config_modifier: Box::new(|_| Ok(())),
        dynamic_gas: dynamic_gas_config1,
    });

    let bootstrap2 = Arc::new(CosmosBootstrap {
        runtime: runtime.clone(),
        cosmos_builder: builder,
        should_randomize_identifiers: true,
        chain_store_dir: "./test-data".into(),
        chain_command_path: chain_command_paths[1 % chain_command_paths.len()]
            .as_str()
            .into(),
        account_prefix: account_prefixes[1 % account_prefixes.len()].as_str().into(),
        staking_denom_prefix: native_tokens[1 % native_tokens.len()].as_str().into(),
        transfer_denom_prefix: "coin".into(),
        genesis_config_modifier: Box::new(|_| Ok(())),
        comet_config_modifier: Box::new(|_| Ok(())),
        dynamic_gas: dynamic_gas_config2,
    });

    let create_client_settings = Settings {
        max_clock_drift: Duration::from_secs(40),
        trusting_period: None,
        trust_threshold: TrustThreshold::ONE_THIRD,
    };

    let setup = CosmosBinaryChannelSetup {
        bootstrap_a: bootstrap1.clone(),
        bootstrap_b: bootstrap2,
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
            let compat_modes = env::var("COMPAT_MODES").ok().map(parse_chain_command_paths);

            let ipv6_grpc = env::var("IPV6_GRPC")
                .ok()
                .map(|val| val == "true")
                .unwrap_or(false);

            let hang_on_fail = env::var("HANG_ON_FAIL")
                .ok()
                .map(|val| val == "1")
                .unwrap_or(false);

            TestConfig {
                chain_command_paths,
                chain_store_dir: Default::default(),
                account_prefixes,
                hang_on_fail,
                bootstrap_with_random_ids: false,
                native_tokens,
                ipv6_grpc,
                compat_modes,
            }
        };

        test_config.chain_command_paths = vec![bootstrap1
            .chain_command_path
            .clone()
            .to_string_lossy()
            .into()];
        test_config.chain_store_dir = bootstrap1.chain_store_dir.clone();

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

        config_modifier(&mut config);

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

        test_method(&driver, relayer_v1_driver).await?;

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
