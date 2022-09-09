use std::time::Duration;

use ibc::core::ics02_client::trust_threshold::TrustThreshold;

use ibc_relayer::config::gas_multiplier::GasMultiplier;
use ibc_relayer::foreign_client::CreateOptions;

use ibc_test_framework::prelude::*;

use ibc_test_framework::bootstrap::binary::chain::{
    add_chain_config, new_registry, spawn_chain_handle,
};

#[test]
fn test_client_default_refresh() -> Result<(), Error> {
    run_binary_chain_test(&ClientDefaultsTest)
}

#[test]
fn test_client_fail_refresh() -> Result<(), Error> {
    run_binary_chain_test(&ClientFailsTest)
}

struct ClientFailsTest;

struct ClientDefaultsTest;

// Override the clients `trusting_period` such that the refresh_window is 40 seconds.
impl TestOverrides for ClientDefaultsTest {
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

impl BinaryChainTest for ClientDefaultsTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let mut client_a_to_b = chains.foreign_clients.client_a_to_b;
        let mut client_b_to_a = chains.foreign_clients.client_b_to_a;
        let res = client_a_to_b.refresh();
        // Check that `refresh()` was successful but did not update the client, as elapsed < refresh_window.
        match res {
            Ok(ibc_events) => assert!(
                ibc_events.is_none(),
                "Client refresh failed: {:?}",
                ibc_events
            ),
            Err(_) => panic!("Client refresh failed: {:?}", res),
        }
        let res = client_b_to_a.refresh();
        // Check that `refresh()` was successful but did not update the client, as elapsed < refresh_window.
        match res {
            Ok(ibc_events) => assert!(
                ibc_events.is_none(),
                "Client refresh failed: {:?}",
                ibc_events
            ),
            Err(_) => panic!("Client refresh failed: {:?}", res),
        }

        // Wait for elapsed > refresh_window
        std::thread::sleep(core::time::Duration::from_secs(40));

        let res = client_a_to_b.refresh();
        // Check that `refresh()` was successful and update client was successful, as elapsed > refresh_window.
        match res {
            Ok(ibc_events) => assert!(
                ibc_events.is_some(),
                "Client refresh failed: {:?}",
                ibc_events
            ),
            Err(_) => panic!("Client refresh failed: {:?}", res),
        }
        let res = client_b_to_a.refresh();
        // Check that `refresh()` was successful and update client was successful, as elapsed > refresh_window.
        match res {
            Ok(ibc_events) => assert!(
                ibc_events.is_some(),
                "Client refresh failed: {:?}",
                ibc_events
            ),
            Err(_) => panic!("Client refresh failed: {:?}", res),
        }
        Ok(())
    }
}

// Override the clients `trusting_period` such that the refresh_window is 40 seconds.
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

impl BinaryChainTest for ClientFailsTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        // Override the configuration in order to use a small `gas_multiplier` which will cause the update client to fail.
        let chains2 = override_connected_chains(chains, |config| {
            config.chains[0].gas_multiplier = Some(GasMultiplier::unsafe_new(0.8));
            config.chains[1].gas_multiplier = Some(GasMultiplier::unsafe_new(0.8));
        })?;

        // Use chains with misconfiguration in order to trigger a ChainError when submitting `MsgClientUpdate`
        // during the refresh call.
        let mut client_a_to_b = chains2.foreign_clients.client_a_to_b;
        let mut client_b_to_a = chains2.foreign_clients.client_b_to_a;

        // Wait for elapsed > refresh_window
        std::thread::sleep(core::time::Duration::from_secs(45));

        let res = client_a_to_b.refresh();
        // Assert that `refresh()` returns an error as the update client will fail due to the low `gas_multiplier`.
        assert!(
            res.is_err(),
            "Client refresh should return an Error {:?}",
            res
        );
        let res = client_b_to_a.refresh();
        // Assert that `refresh()` returns an error as the update client will fail due to the low `gas_multiplier`.
        assert!(
            res.is_err(),
            "Client refresh should return an Error {:?}",
            res
        );
        Ok(())
    }
}

fn override_connected_chains<ChainA, ChainB>(
    chains: ConnectedChains<ChainA, ChainB>,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ConnectedChains<impl ChainHandle, impl ChainHandle>, Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let mut config = Config::default();

    add_chain_config(&mut config, chains.node_a.value())?;
    add_chain_config(&mut config, chains.node_b.value())?;

    config_modifier(&mut config);

    let registry = new_registry(config.clone());

    // Pass in unique closure expressions `||{}` as the first argument so that
    // the returned chains are considered different types by Rust.
    // See [`spawn_chain_handle`] for more details.
    let handle_a = spawn_chain_handle(|| {}, &registry, chains.node_a.value())?;
    let handle_b = spawn_chain_handle(|| {}, &registry, chains.node_b.value())?;

    let foreign_clients = restore_foreign_client_pair(
        &handle_a,
        &handle_b,
        chains.foreign_clients.client_id_a().value(),
        chains.foreign_clients.client_id_b().value(),
    )?;

    let chains = ConnectedChains::new(
        handle_a,
        handle_b,
        chains.node_a.retag(),
        chains.node_b.retag(),
        foreign_clients,
    );

    Ok(chains)
}

fn restore_foreign_client_pair<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    client_id_a: &ClientId,
    client_id_b: &ClientId,
) -> Result<ForeignClientPair<ChainA, ChainB>, Error> {
    let client_a_to_b =
        ForeignClient::restore(client_id_b.clone(), chain_b.clone(), chain_a.clone());

    let client_b_to_a =
        ForeignClient::restore(client_id_a.clone(), chain_a.clone(), chain_b.clone());

    Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
}
