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
use prost::Message;
use std::str::FromStr;

use ibc_proto::cosmos::gov::v1beta1::{query_client::QueryClient, QueryProposalRequest};
use ibc_proto::ibc::core::client::v1::UpgradeProposal;
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::upgrade_chain::{build_and_send_ibc_upgrade_proposal, UpgradePlanOptions};
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_test_framework::{chain::cli::upgrade::vote_proposal, prelude::*};

const MAX_DEPOSIT_PERIOD: &str = "10s";
const VOTING_PERIOD: &str = "10s";
const DELTA_HEIGHT: u64 = 15;

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

struct ClientUpgradeTest;

impl TestOverrides for ClientUpgradeTest {
    /// Update the genesis file in order to reduce the time required to upgrade the chain.
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        use serde_json::Value;

        let max_deposit_periods = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("deposit_params"))
            .and_then(|deposit_params| deposit_params.as_object_mut());

        if let Some(max_deposit_period) = max_deposit_periods {
            max_deposit_period.insert(
                "max_deposit_period".to_owned(),
                Value::String(MAX_DEPOSIT_PERIOD.to_string()),
            );
        } else {
            return Err(Error::generic(eyre!(
                "failed to update max_deposit_period in genesis file"
            )));
        }

        let voting_period = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("voting_params"))
            .and_then(|voting_params| voting_params.as_object_mut());

        if let Some(voting_period) = voting_period {
            voting_period.insert(
                "voting_period".to_owned(),
                Value::String(VOTING_PERIOD.to_string()),
            );
            Ok(())
        } else {
            Err(Error::generic(eyre!(
                "failed to update voting_period in genesis file"
            )))
        }
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

        let src_chain_config = chains.handle_b().config().unwrap();
        let dst_chain_config = chains.handle_a().config().unwrap();

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        // Create and send an chain upgrade proposal
        let opts = UpgradePlanOptions {
            dst_chain_config,
            src_chain_config,
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
        std::thread::sleep(core::time::Duration::from_secs(2));

        let driver = chains.node_a.chain_driver().0;

        // Retrieve the height which should be used to upgrade the client
        let upgrade_height = driver
            .runtime
            .block_on(query_upgrade_proposal_height(
                &Uri::from_str(&driver.grpc_address()).unwrap(),
                1,
            ))
            .unwrap();

        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            upgrade_height,
        )
        .unwrap();

        // Vote on the proposal so the chain will upgrade
        vote_proposal(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        // The application height reports a height of 1 less than the height according to Tendermint
        let target_reference_application_height = client_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        let mut reference_application_latest_height = foreign_clients
            .client_a_to_b
            .src_chain()
            .query_latest_height()
            .ok()
            .unwrap();

        while reference_application_latest_height != target_reference_application_height {
            std::thread::sleep(core::time::Duration::from_millis(500));

            reference_application_latest_height = foreign_clients
                .client_a_to_b
                .src_chain()
                .query_latest_height()
                .ok()
                .unwrap();
        }

        // Wait for the chain to upgrade
        std::thread::sleep(core::time::Duration::from_secs(6));

        // Trigger the client upgrade
        let outcome = foreign_clients.client_a_to_b.upgrade(client_upgrade_height);

        assert!(outcome.is_ok(), "{:?}", outcome);

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
        .unwrap();

        // Wait a bit before trying to upgrade the client
        std::thread::sleep(core::time::Duration::from_secs(2));

        // Trigger the client upgrade
        let outcome = foreign_clients.client_a_to_b.upgrade(client_upgrade_height);

        assert!(outcome.is_err(), "{:?}", outcome);

        Ok(())
    }
}

struct HeightTooHighClientUpgradeTest;

impl TestOverrides for HeightTooHighClientUpgradeTest {
    /// Update the genesis file in order to reduce the time required to upgrade the chain
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        use serde_json::Value;

        let max_deposit_periods = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("deposit_params"))
            .and_then(|deposit_params| deposit_params.as_object_mut());

        if let Some(max_deposit_period) = max_deposit_periods {
            max_deposit_period.insert(
                "max_deposit_period".to_owned(),
                Value::String(MAX_DEPOSIT_PERIOD.to_string()),
            );
        } else {
            return Err(Error::generic(eyre!(
                "failed to update max_deposit_period in genesis file"
            )));
        }

        let voting_period = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("voting_params"))
            .and_then(|voting_params| voting_params.as_object_mut());

        if let Some(voting_period) = voting_period {
            voting_period.insert(
                "voting_period".to_owned(),
                Value::String(VOTING_PERIOD.to_string()),
            );
            Ok(())
        } else {
            Err(Error::generic(eyre!(
                "failed to update voting_period in genesis file"
            )))
        }
    }
}

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

        let src_chain_config = chains.handle_b().config().unwrap();
        let dst_chain_config = chains.handle_a().config().unwrap();

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        // Create and send an chain upgrade proposal
        let opts = UpgradePlanOptions {
            dst_chain_config,
            src_chain_config,
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
        std::thread::sleep(core::time::Duration::from_secs(2));

        let driver = chains.node_a.chain_driver().0;

        // Retrieve the height which should be used to upgrade the client
        let upgrade_height = driver
            .runtime
            .block_on(query_upgrade_proposal_height(
                &Uri::from_str(&driver.grpc_address()).unwrap(),
                1,
            ))
            .unwrap();

        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            upgrade_height,
        )
        .unwrap();

        // Vote on the proposal so the chain will upgrade
        vote_proposal(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        // The application height reports a height of 1 less than the height according to Tendermint
        let target_reference_application_height = client_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        let mut reference_application_latest_height = foreign_clients
            .client_a_to_b
            .src_chain()
            .query_latest_height()
            .ok()
            .unwrap();

        while reference_application_latest_height != target_reference_application_height {
            std::thread::sleep(core::time::Duration::from_millis(500));

            reference_application_latest_height = foreign_clients
                .client_a_to_b
                .src_chain()
                .query_latest_height()
                .ok()
                .unwrap();
        }

        // Wait for the chain to upgrade
        std::thread::sleep(core::time::Duration::from_secs(6));

        // Trigger the client upgrade using client_upgrade_height + 1.
        let outcome = foreign_clients
            .client_a_to_b
            .upgrade(client_upgrade_height.increment());

        assert!(outcome.is_err(), "{:?}", outcome);

        Ok(())
    }
}

struct HeightTooLowClientUpgradeTest;

impl TestOverrides for HeightTooLowClientUpgradeTest {
    /// Update the genesis file in order to reduce the time required to upgrade the chain.
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        use serde_json::Value;

        let max_deposit_periods = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("deposit_params"))
            .and_then(|deposit_params| deposit_params.as_object_mut());

        if let Some(max_deposit_period) = max_deposit_periods {
            max_deposit_period.insert(
                "max_deposit_period".to_owned(),
                Value::String(MAX_DEPOSIT_PERIOD.to_string()),
            );
        } else {
            return Err(Error::generic(eyre!(
                "failed to update max_deposit_period in genesis file"
            )));
        }

        let voting_period = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("voting_params"))
            .and_then(|voting_params| voting_params.as_object_mut());

        if let Some(voting_period) = voting_period {
            voting_period.insert(
                "voting_period".to_owned(),
                Value::String(VOTING_PERIOD.to_string()),
            );
            Ok(())
        } else {
            Err(Error::generic(eyre!(
                "failed to update voting_period in genesis file"
            )))
        }
    }
}

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

        let src_chain_config = chains.handle_b().config().unwrap();
        let dst_chain_config = chains.handle_a().config().unwrap();

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        // Create and send an chain upgrade proposal
        let opts = UpgradePlanOptions {
            dst_chain_config,
            src_chain_config,
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
        std::thread::sleep(core::time::Duration::from_secs(2));

        let driver = chains.node_a.chain_driver().0;

        // Retrieve the height which should be used to upgrade the client
        let upgrade_height = driver
            .runtime
            .block_on(query_upgrade_proposal_height(
                &Uri::from_str(&driver.grpc_address()).unwrap(),
                1,
            ))
            .unwrap();

        let client_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            upgrade_height,
        )
        .unwrap();

        // Vote on the proposal so the chain will upgrade
        vote_proposal(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        // The application height reports a height of 1 less than the height according to Tendermint
        let target_reference_application_height = client_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        let mut reference_application_latest_height = foreign_clients
            .client_a_to_b
            .src_chain()
            .query_latest_height()
            .ok()
            .unwrap();

        while reference_application_latest_height != target_reference_application_height {
            std::thread::sleep(core::time::Duration::from_millis(500));

            reference_application_latest_height = foreign_clients
                .client_a_to_b
                .src_chain()
                .query_latest_height()
                .ok()
                .unwrap();
        }

        // Wait for the chain to upgrade
        std::thread::sleep(core::time::Duration::from_secs(6));

        // Trigger the client upgrade using client_upgrade_height - 1.
        let outcome = foreign_clients
            .client_a_to_b
            .upgrade(client_upgrade_height.decrement().unwrap());

        assert!(outcome.is_err(), "{:?}", outcome);

        Ok(())
    }
}

/// Query the proposal with the given proposal_id, which is supposed to be an UpgradeProposal.
/// Extract the Plan from the UpgradeProposal and get the height at which the chain upgrades,
/// from the Plan.
pub async fn query_upgrade_proposal_height(
    grpc_address: &Uri,
    proposal_id: u64,
) -> Result<u64, Error> {
    let mut client = match QueryClient::connect(grpc_address.clone()).await {
        Ok(client) => client,
        Err(_) => {
            return Err(Error::query_client());
        }
    };

    let request = tonic::Request::new(QueryProposalRequest { proposal_id });

    let response = client
        .proposal(request)
        .await
        .map(|r| r.into_inner())
        .map_err(RelayerError::grpc_status)?;

    // Querying for a balance might fail, i.e. if the account doesn't actually exist
    let proposal = response
        .proposal
        .ok_or_else(|| RelayerError::empty_query_account(proposal_id.to_string()))?;

    match proposal.content {
        Some(content) => {
            if content.type_url != *"/ibc.core.client.v1.UpgradeProposal" {
                return Err(Error::incorrect_proposal_type_url(content.type_url));
            }
            let raw_upgrade_proposal: &[u8] = &content.value;
            match UpgradeProposal::decode(raw_upgrade_proposal) {
                Ok(upgrade_proposal) => match upgrade_proposal.plan {
                    Some(plan) => {
                        let h = plan.height;
                        Ok(h as u64)
                    }
                    None => Err(Error::empty_plan()),
                },
                Err(_e) => Err(Error::incorrect_proposal()),
            }
        }
        None => Err(Error::empty_proposal()),
    }
}
