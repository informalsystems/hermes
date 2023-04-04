//! This test tests four different cases:
//!
//! - The `ClientUpgradeTest` tests the case where the client upgrade works
//!   correctly after the chain was upgraded.
//!
//! - The `InvalidClientUpgradeTest` tests the case where the
//!   client upgrade fails as the chain has not been upgraded.
//!
//! - The `HeightTooHighClientUpgradeTest`tests the case where the client
//!   fails to upgrade because a height too big is given as input.
//!
//! - The `test_height_too_low_client_upgrade`tests the case where the client
//!   fails to upgrade because a height too small is given as input.

use http::Uri;
use std::str::FromStr;

use ibc_relayer::upgrade_chain::{build_and_send_ibc_upgrade_proposal, UpgradePlanOptions};
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_test_framework::{
    chain::{
        config::{set_max_deposit_period, set_voting_period},
        ext::wait_chain::wait_for_chain_height,
    },
    prelude::*,
};

const MAX_DEPOSIT_PERIOD: &str = "10s";
const VOTING_PERIOD: &str = "10s";
const DELTA_HEIGHT: u64 = 15;
const WAIT_CHAIN_UPGRADE: Duration = Duration::from_secs(4);
const MAX_WAIT_FOR_CHAIN_HEIGHT: Duration = Duration::from_secs(60);

#[test]
fn test_client_upgrade() -> Result<(), Error> {
    run_binary_chain_test(&ClientUpgradeTest)
}

#[test]
fn test_invalid_client_upgrade() -> Result<(), Error> {
    run_binary_chain_test(&InvalidClientUpgradeTest)
}

#[test]
fn test_height_too_high_client_upgrade() -> Result<(), Error> {
    run_binary_chain_test(&HeightTooHighClientUpgradeTest)
}

#[test]
fn test_height_too_low_client_upgrade() -> Result<(), Error> {
    run_binary_chain_test(&HeightTooLowClientUpgradeTest)
}

struct ClientUpgradeTestOverrides;

struct ClientUpgradeTest;

impl TestOverrides for ClientUpgradeTestOverrides {
    /// Update the genesis file in order to reduce the time required to upgrade the chain.
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        set_max_deposit_period(genesis, MAX_DEPOSIT_PERIOD)?;
        set_voting_period(genesis, VOTING_PERIOD)?;
        Ok(())
    }
}

impl BinaryChainTest for ClientUpgradeTest {
    fn run<
        ChainA: ibc_test_framework::prelude::ChainHandle,
        ChainB: ibc_test_framework::prelude::ChainHandle,
    >(
        &self,
        _config: &ibc_test_framework::prelude::TestConfig,
        _relayer: ibc_test_framework::prelude::RelayerDriver,
        chains: ibc_test_framework::prelude::ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), ibc_test_framework::prelude::Error> {
        let foreign_clients = chains.clone().foreign_clients;

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        // Create and send an chain upgrade proposal
        let opts = UpgradePlanOptions {
            src_client_id,
            amount: 10000000u64,
            denom: "stake".to_string(),
            height_offset: DELTA_HEIGHT,
            upgraded_chain_id,
            upgraded_unbonding_period: None,
            upgrade_plan_name: "plan".to_string(),
        };

        build_and_send_ibc_upgrade_proposal(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            &opts,
        )
        .map_err(Error::upgrade_chain)?;

        // Wait for the proposal to be processed
        std::thread::sleep(Duration::from_secs(2));

        let driver = chains.node_a.chain_driver();

        // Retrieve the height which should be used to upgrade the client
        let upgrade_height = driver.query_upgrade_proposal_height(
            &Uri::from_str(&driver.0.grpc_address()).map_err(handle_generic_error)?,
            1,
        )?;

        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            upgrade_height,
        )
        .map_err(handle_generic_error)?;

        // Vote on the proposal so the chain will upgrade
        driver.vote_proposal("1200stake")?;

        // The application height reports a height of 1 less than the height according to Tendermint
        let target_reference_application_height = client_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        assert!(wait_for_chain_height(
            &foreign_clients,
            target_reference_application_height,
            MAX_WAIT_FOR_CHAIN_HEIGHT
        )
        .is_ok());

        // Wait for the chain to upgrade
        std::thread::sleep(WAIT_CHAIN_UPGRADE);

        // Trigger the client upgrade
        let outcome = foreign_clients.client_a_to_b.upgrade(client_upgrade_height);

        assert!(outcome.is_ok(), "{outcome:?}");

        Ok(())
    }
}

struct InvalidClientUpgradeTest;

/// The genesis file doesn't need to be updated since the chain isn't upgraded
/// for this test.
impl TestOverrides for InvalidClientUpgradeTest {}

impl BinaryChainTest for InvalidClientUpgradeTest {
    fn run<
        ChainA: ibc_test_framework::prelude::ChainHandle,
        ChainB: ibc_test_framework::prelude::ChainHandle,
    >(
        &self,
        _config: &ibc_test_framework::prelude::TestConfig,
        _relayer: ibc_test_framework::prelude::RelayerDriver,
        chains: ibc_test_framework::prelude::ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), ibc_test_framework::prelude::Error> {
        let arbitrary_height = 5u64;
        let foreign_clients = chains.foreign_clients;

        // Wait for the chain to reach a given height
        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            arbitrary_height,
        )
        .map_err(handle_generic_error)?;

        // Wait a bit before trying to upgrade the client
        std::thread::sleep(Duration::from_secs(2));

        // Trigger the client upgrade
        let outcome = foreign_clients.client_a_to_b.upgrade(client_upgrade_height);

        assert!(outcome.is_err(), "{outcome:?}");

        Ok(())
    }
}

struct HeightTooHighClientUpgradeTest;

impl BinaryChainTest for HeightTooHighClientUpgradeTest {
    fn run<
        ChainA: ibc_test_framework::prelude::ChainHandle,
        ChainB: ibc_test_framework::prelude::ChainHandle,
    >(
        &self,
        _config: &ibc_test_framework::prelude::TestConfig,
        _relayer: ibc_test_framework::prelude::RelayerDriver,
        chains: ibc_test_framework::prelude::ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), ibc_test_framework::prelude::Error> {
        let foreign_clients = chains.clone().foreign_clients;

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        // Create and send an chain upgrade proposal
        let opts = UpgradePlanOptions {
            src_client_id,
            amount: 10000000u64,
            denom: "stake".to_string(),
            height_offset: DELTA_HEIGHT,
            upgraded_chain_id,
            upgraded_unbonding_period: None,
            upgrade_plan_name: "plan".to_string(),
        };

        build_and_send_ibc_upgrade_proposal(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            &opts,
        )
        .map_err(Error::upgrade_chain)?;

        // Wait for the proposal to be processed
        std::thread::sleep(Duration::from_secs(2));

        let driver = chains.node_a.chain_driver();

        // Retrieve the height which should be used to upgrade the client
        let upgrade_height = driver.query_upgrade_proposal_height(
            &Uri::from_str(&driver.0.grpc_address()).map_err(handle_generic_error)?,
            1,
        )?;

        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            upgrade_height,
        )
        .map_err(handle_generic_error)?;

        // Vote on the proposal so the chain will upgrade
        driver.vote_proposal("1200stake")?;

        // The application height reports a height of 1 less than the height according to Tendermint
        let target_reference_application_height = client_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        assert!(wait_for_chain_height(
            &foreign_clients,
            target_reference_application_height,
            MAX_WAIT_FOR_CHAIN_HEIGHT
        )
        .is_ok());

        // Wait for the chain to upgrade
        std::thread::sleep(WAIT_CHAIN_UPGRADE);

        // Trigger the client upgrade using client_upgrade_height + 1.
        let outcome = foreign_clients
            .client_a_to_b
            .upgrade(client_upgrade_height.increment());

        assert!(outcome.is_err(), "{outcome:?}");

        Ok(())
    }
}

struct HeightTooLowClientUpgradeTest;

impl BinaryChainTest for HeightTooLowClientUpgradeTest {
    fn run<
        ChainA: ibc_test_framework::prelude::ChainHandle,
        ChainB: ibc_test_framework::prelude::ChainHandle,
    >(
        &self,
        _config: &ibc_test_framework::prelude::TestConfig,
        _relayer: ibc_test_framework::prelude::RelayerDriver,
        chains: ibc_test_framework::prelude::ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), ibc_test_framework::prelude::Error> {
        let foreign_clients = chains.clone().foreign_clients;

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        // Create and send an chain upgrade proposal
        let opts = UpgradePlanOptions {
            src_client_id,
            amount: 10000000u64,
            denom: "stake".to_string(),
            height_offset: DELTA_HEIGHT,
            upgraded_chain_id,
            upgraded_unbonding_period: None,
            upgrade_plan_name: "plan".to_string(),
        };

        build_and_send_ibc_upgrade_proposal(
            chains.handle_a().clone(),
            chains.handle_b().clone(),
            &opts,
        )
        .map_err(Error::upgrade_chain)?;

        // Wait for the proposal to be processed
        std::thread::sleep(Duration::from_secs(2));

        let driver = chains.node_a.chain_driver();

        // Retrieve the height which should be used to upgrade the client
        let upgrade_height = driver.query_upgrade_proposal_height(
            &Uri::from_str(&driver.0.grpc_address()).map_err(handle_generic_error)?,
            1,
        )?;

        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            upgrade_height,
        )
        .map_err(handle_generic_error)?;

        // Vote on the proposal so the chain will upgrade
        driver.vote_proposal("1200stake")?;

        // The application height reports a height of 1 less than the height according to Tendermint
        let target_reference_application_height = client_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        assert!(wait_for_chain_height(
            &foreign_clients,
            target_reference_application_height,
            MAX_WAIT_FOR_CHAIN_HEIGHT
        )
        .is_ok());

        // Wait for the chain to upgrade
        std::thread::sleep(WAIT_CHAIN_UPGRADE);

        // Trigger the client upgrade using client_upgrade_height - 1.
        let outcome = foreign_clients.client_a_to_b.upgrade(
            client_upgrade_height
                .decrement()
                .map_err(handle_generic_error)?,
        );

        assert!(outcome.is_err(), "{outcome:?}");

        Ok(())
    }
}

impl HasOverrides for ClientUpgradeTest {
    type Overrides = ClientUpgradeTestOverrides;

    fn get_overrides(&self) -> &ClientUpgradeTestOverrides {
        &ClientUpgradeTestOverrides
    }
}

impl HasOverrides for HeightTooLowClientUpgradeTest {
    type Overrides = ClientUpgradeTestOverrides;

    fn get_overrides(&self) -> &ClientUpgradeTestOverrides {
        &ClientUpgradeTestOverrides
    }
}

impl HasOverrides for HeightTooHighClientUpgradeTest {
    type Overrides = ClientUpgradeTestOverrides;

    fn get_overrides(&self) -> &ClientUpgradeTestOverrides {
        &ClientUpgradeTestOverrides
    }
}
