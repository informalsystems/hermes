use ibc_relayer::upgrade_chain::{build_and_send_ibc_upgrade_proposal, UpgradePlanOptions};
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_test_framework::{
    chain::cli::upgrade::{query_proposal, vote_proposal},
    prelude::*,
};

#[test]
fn test_client_upgrade() -> Result<(), Error> {
    run_binary_chain_test(&ClientUpgradeTest)
}

struct ClientUpgradeTest;

impl TestOverrides for ClientUpgradeTest {
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
                Value::String("20s".to_string()),
            );
        } else {
            return Err(Error::generic(eyre!(
                "failed to update max_deposit_period in genesis file"
            )));
        }

        let max_deposit_periods = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("voting_params"))
            .and_then(|voting_params| voting_params.as_object_mut());

        if let Some(max_deposit_period) = max_deposit_periods {
            max_deposit_period.insert("voting_period".to_owned(), Value::String("20s".to_string()));
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
        let chain_upgrade_height = 50u64;
        let foreign_clients = chains.clone().foreign_clients;

        let src_chain_config = chains.handle_b().config().unwrap();
        let dst_chain_config = chains.handle_a().config().unwrap();

        let upgraded_chain_id = chains.chain_id_a().0.clone();

        let src_client_id = foreign_clients.client_id_b().0.clone();

        let opts = UpgradePlanOptions {
            dst_chain_config,
            src_chain_config,
            src_client_id,
            amount: 10000000u64,
            denom: "stake".to_string(),
            height_offset: chain_upgrade_height,
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

        query_proposal(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        // Vote on the proposal so the chain will upgrade
        vote_proposal(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        // Similar to the method used in the CLI `hermes upgrade client` we wait for
        // the chain to reach the height at which it upgrades before trying to upgrade
        // the client.
        let reference_upgrade_height = Height::new(
            foreign_clients.client_a_to_b.src_chain().id().version(),
            chain_upgrade_height,
        )
        .unwrap();

        let target_reference_application_height = reference_upgrade_height
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

            println!(
                "Reference application latest height: {}",
                reference_application_latest_height
            );
        }

        // Wait for the chain to upgrade.
        std::thread::sleep(core::time::Duration::from_secs(6));

        query_proposal(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        // Trigger the client upgrade.
        let outcome = foreign_clients
            .client_a_to_b
            .upgrade(reference_upgrade_height);

        assert!(outcome.is_ok(), "{:?}", outcome);

        Ok(())
    }
}
