use std::time::Duration;

use ibc::core::ics02_client::trust_threshold::TrustThreshold;

use ibc_relayer::config::types::GasMultiplier;
use ibc_relayer::foreign_client::CreateOptions;

use ibc_test_framework::prelude::*;

use ibc_test_framework::bootstrap::binary::chain::{
    bootstrap_chains_with_full_nodes, bootstrap_chains_with_full_nodes_and_existing_clients,
    BootstrapClientOptions,
};
use ibc_test_framework::types::binary::chains::DropChainHandle;
use ibc_test_framework::types::env::write_env;

#[test]
fn test_client_default_refresh() -> Result<(), Error> {
    run_binary_chain_test(&ClientDefaultsTest)
}

#[test]
fn test_client_fail_refresh() -> Result<(), Error> {
    run_binary_node_test(&ClientFailsTest)
}

struct ClientFailsTest;

struct ClientDefaultsTest;

impl TestOverrides for ClientDefaultsTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.chains[0].clock_drift = Duration::from_secs(3);
        config.chains[0].max_block_time = Duration::from_secs(5);
        config.chains[0].trusting_period = Some(Duration::from_secs(120_000));
        config.chains[0].trust_threshold = TrustThreshold::new(13, 23).unwrap().try_into().unwrap();

        config.chains[1].clock_drift = Duration::from_secs(6);
        config.chains[1].max_block_time = Duration::from_secs(15);
        config.chains[1].trusting_period = Some(Duration::from_secs(340_000));
        config.chains[1].trust_threshold = TrustThreshold::TWO_THIRDS.try_into().unwrap();
    }
}

impl BinaryChainTest for ClientDefaultsTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let mut client = chains.foreign_clients.client_a_to_b;
        let res = client.refresh();
        assert!(res.is_ok(), "Client refresh failed {:?}", res);

        let mut client = chains.foreign_clients.client_b_to_a;
        let res = client.refresh();
        assert!(res.is_ok(), "Client refresh failed {:?}", res);
        Ok(())
    }
}

impl TestOverrides for ClientFailsTest {
    fn client_options_a_to_b(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(3)),
            trusting_period: Some(Duration::from_secs(60)),
            trust_threshold: Some(TrustThreshold::new(13, 23).unwrap()),
        }
    }

    fn client_options_b_to_a(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(6)),
            trusting_period: Some(Duration::from_secs(60)),
            trust_threshold: Some(TrustThreshold::TWO_THIRDS),
        }
    }
}

impl ClientFailsTest {
    fn client_options_a_to_b(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(3)),
            trusting_period: Some(Duration::from_secs(60)),
            trust_threshold: Some(TrustThreshold::new(13, 23).unwrap()),
        }
    }

    fn client_options_b_to_a(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(6)),
            trusting_period: Some(Duration::from_secs(60)),
            trust_threshold: Some(TrustThreshold::TWO_THIRDS),
        }
    }
}

impl BinaryNodeTest for ClientFailsTest {
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error> {
        // Bootstrap chains and create new clients using a correct configuration.
        // This is done because creating new clients requires relaying `MsgCreateClient` which require a
        // correct configuration.
        let bootstrap_options = BootstrapClientOptions::default()
            .client_options_a_to_b(self.client_options_a_to_b())
            .client_options_b_to_a(self.client_options_b_to_a())
            .bootstrap_with_random_ids(config.bootstrap_with_random_ids);

        let (_, chains) = bootstrap_chains_with_full_nodes(
            config,
            node_a.clone(),
            node_b.clone(),
            bootstrap_options,
            |_config| (),
        )?;

        let _drop_handle_a = DropChainHandle(chains.handle_a.clone());
        let _drop_handle_b = DropChainHandle(chains.handle_b.clone());

        // Bootstrap chains using misconfiguration and get existing clients instead of creating new ones.
        // This is done because creating new clients requires relaying `MsgCreateClient` which would fail
        // with the misconfiguration.
        let bootstrap_options = BootstrapClientOptions::default()
            .client_options_a_to_b(self.client_options_a_to_b())
            .client_options_b_to_a(self.client_options_b_to_a())
            .bootstrap_with_random_ids(config.bootstrap_with_random_ids);

        let (relayer, chains) = bootstrap_chains_with_full_nodes_and_existing_clients(
            config,
            node_a.clone(),
            node_b.clone(),
            bootstrap_options,
            |config| {
                config.chains[0].gas_multiplier = Some(GasMultiplier::new(0.8));
                config.chains[1].gas_multiplier = Some(GasMultiplier::new(0.8));
            },
            chains.foreign_clients.client_a_to_b.id(),
            chains.foreign_clients.client_b_to_a.id(),
        )?;

        let env_path = config.chain_store_dir.join("binary-chains.env");

        write_env(&env_path, &(&relayer, &chains))?;

        info!("written chains environment to {}", env_path.display());

        // Use chains with misconfiguration in order to trigger a ChainError when submitting `MsgClientUpdate`
        // during the refresh call.
        let mut client = chains.foreign_clients.client_a_to_b;
        // Wait for elapsd > refresh_window
        std::thread::sleep(core::time::Duration::from_secs(40));
        let res = client.refresh();
        assert!(
            res.is_err(),
            "Client refresh should return an Error {:?}",
            res
        );

        let mut client = chains.foreign_clients.client_b_to_a;
        let res = client.refresh();
        assert!(
            res.is_err(),
            "Client refresh should return an Error {:?}",
            res
        );
        Ok(())
    }
}
