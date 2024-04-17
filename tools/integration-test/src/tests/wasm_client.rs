use core::time::Duration;
use std::path::Path;
use std::thread::sleep;

use ibc_relayer::foreign_client::{
    CreateOptions, ForeignClientError, TendermintCreateOptions, WasmCreateOptions,
};
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::events::IbcEvent;
use ibc_test_framework::bootstrap::binary::chain::{
    add_chain_config, bootstrap_foreign_client, new_registry, save_relayer_config,
    spawn_chain_handle,
};
use ibc_test_framework::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use ibc_test_framework::chain::ext::wasm_client::StoreWasmClientCodeMethodsExt;
use ibc_test_framework::prelude::*;
use ibc_test_framework::types::binary::chains::DropChainHandle;
use ibc_test_framework::types::env::write_env;
use ibc_test_framework::util::proposal_status::ProposalStatus;

const WASM_PATH: &str = "fixtures/wasm/ibc_client_tendermint_cw.wasm";

const TM_CREATE_OPTIONS: TendermintCreateOptions = TendermintCreateOptions {
    max_clock_drift: Some(Duration::from_secs(3)),
    trusting_period: Some(Duration::from_secs(30)),
    trust_threshold: Some(TrustThreshold::TWO_THIRDS),
};

#[test]
fn test_create_and_update_wasm_client() -> Result<(), Error> {
    run_binary_node_test(&CreateAndUpdateWasmClientTest)
}

fn sha256(data: &[u8]) -> Vec<u8> {
    use sha2::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(data);
    hasher.finalize().to_vec()
}

struct CreateAndUpdateWasmClientTest;

impl TestOverrides for CreateAndUpdateWasmClientTest {
    fn client_options_a_to_b(&self) -> CreateOptions {
        let wasm_code = std::fs::read(WASM_PATH).unwrap();
        let checksum = sha256(&wasm_code);

        WasmCreateOptions {
            checksum,
            underlying: TM_CREATE_OPTIONS.into(),
        }
        .into()
    }

    fn client_options_b_to_a(&self) -> CreateOptions {
        let wasm_code = std::fs::read(WASM_PATH).unwrap();
        let checksum = sha256(&wasm_code);

        WasmCreateOptions {
            checksum,
            underlying: TM_CREATE_OPTIONS.into(),
        }
        .into()
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        let max_deposit_period = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("params"))
            .and_then(|deposit_params| deposit_params.as_object_mut())
            .ok_or_else(|| eyre!("Failed to retrieve `deposit_params` in genesis configuration"))?;

        max_deposit_period
            .insert(
                "max_deposit_period".to_owned(),
                serde_json::Value::String("10s".to_owned()),
            )
            .ok_or_else(|| {
                eyre!("Failed to update `max_deposit_period` in genesis configuration")
            })?;

        let voting_period = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("gov"))
            .and_then(|gov| gov.get_mut("params"))
            .and_then(|voting_params| voting_params.as_object_mut())
            .ok_or_else(|| eyre!("Failed to retrieve `voting_params` in genesis configuration"))?;

        voting_period
            .insert(
                "voting_period".to_owned(),
                serde_json::Value::String("10s".to_owned()),
            )
            .ok_or_else(|| eyre!("Failed to update `voting_period` in genesis configuration"))?;

        let allowed_clients = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("ibc"))
            .and_then(|ibc| ibc.get_mut("client_genesis"))
            .and_then(|client_genesis| client_genesis.get_mut("params"))
            .and_then(|params| params.get_mut("allowed_clients"))
            .and_then(|allowed_clients| allowed_clients.as_array_mut())
            .ok_or_else(|| {
                eyre!("Failed to retrieve `allowed_clients` in genesis configuration")
            })?;

        allowed_clients.push(serde_json::Value::String("08-wasm".to_string()));

        Ok(())
    }

    fn modify_node_config(&self, config: &mut toml::Value) -> Result<(), Error> {
        config
            .get_mut("rpc")
            .and_then(|rpc| rpc.as_table_mut())
            .ok_or_else(|| eyre!("Failed to retrieve `rpc` in app configuration"))?
            .insert(
                "max_body_bytes".to_string(),
                toml::Value::Integer(10001048576),
            );

        Ok(())
    }
}

impl BinaryNodeTest for CreateAndUpdateWasmClientTest {
    fn run(
        &self,
        test_config: &TestConfig,
        node_a: FullNode,
        node_b: FullNode,
    ) -> Result<(), Error> {
        let (chain_a, chain_b) = setup_chains(test_config, &node_a, &node_b)?;

        let _drop_handle_a = DropChainHandle(chain_a.clone());
        let _drop_handle_b = DropChainHandle(chain_b.clone());

        info!("Storing Wasm contract on chain A");
        store_wasm_contract(node_a, test_config)?;

        info!("Storing Wasm contract on chain B");
        store_wasm_contract(node_b, test_config)?;

        let overrides = self.get_overrides();

        info!("Creating client A to B");
        let mut client_a_to_b =
            bootstrap_foreign_client(&chain_a, &chain_b, overrides.client_options_a_to_b())?;

        info!("Creating client B to A");
        let mut client_b_to_a =
            bootstrap_foreign_client(&chain_b, &chain_a, overrides.client_options_b_to_a())?;

        let res = client_a_to_b.refresh();

        // Check that `refresh()` was successful but did not update the client, as elapsed < refresh_window.
        assert_client_refreshed(false, res);
        info!("Client A to B was not refreshed, as expected");

        let res = client_b_to_a.refresh();

        // Check that `refresh()` was successful but did not update the client, as elapsed < refresh_window.
        assert_client_refreshed(false, res);
        info!("Client B to A was not refreshed, as expected");

        // Wait for elapsed > refresh_window
        sleep(Duration::from_secs(20));

        let res = client_a_to_b.refresh();

        // Check that `refresh()` was successful and update client was successful, as elapsed > refresh_window.
        assert_client_refreshed(true, res);
        info!("Client A to B was refreshed successfully");

        let res = client_b_to_a.refresh();

        // Check that `refresh()` was successful and update client was successful, as elapsed > refresh_window.
        assert_client_refreshed(true, res);
        info!("Client B to A was refreshed successfully");

        Ok(())
    }
}

fn store_wasm_contract(node_a: FullNode, test_config: &TestConfig) -> Result<(), Error> {
    node_a
        .chain_driver
        .store_wasm_client_code(Path::new(WASM_PATH), "tmp", "tmp", "validator")?;

    node_a
        .chain_driver
        .assert_proposal_status(ProposalStatus::DepositPeriod, "1")?;

    node_a
        .chain_driver
        .deposit_proposal("1", "100000000stake")?;

    node_a
        .chain_driver
        .assert_proposal_status(ProposalStatus::VotingPeriod, "1")?;

    let fee_denom_a = &test_config.native_tokens[0];
    node_a
        .chain_driver
        .vote_proposal("1", &format!("381000000{}", fee_denom_a))?;

    node_a
        .chain_driver
        .assert_proposal_status(ProposalStatus::Passed, "1")?;

    Ok(())
}

fn setup_chains(
    test_config: &TestConfig,
    node_a: &FullNode,
    node_b: &FullNode,
) -> Result<(impl ChainHandle, impl ChainHandle), Error> {
    let env_path = test_config.chain_store_dir.join("binary-chains.env");

    let mut config = Config::default();

    add_chain_config(&mut config, node_a, test_config, 0)?;
    add_chain_config(&mut config, node_b, test_config, 1)?;

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");
    save_relayer_config(&config, &config_path)?;

    let registry = new_registry(config.clone());
    let chain_a = spawn_chain_handle(|| {}, &registry, node_a)?;
    let chain_b = spawn_chain_handle(|| {}, &registry, node_b)?;

    sleep(Duration::from_secs(10));

    let relayer = RelayerDriver {
        config_path,
        config,
        registry,
        hang_on_fail: test_config.hang_on_fail,
    };

    write_env(&env_path, &relayer)?;
    info!("written chains environment to {}", env_path.display());

    Ok((chain_a, chain_b))
}

fn assert_client_refreshed(
    refreshed: bool,
    res: Result<Option<Vec<IbcEvent>>, ForeignClientError>,
) {
    match res {
        Ok(ibc_events) if refreshed => assert!(
            ibc_events.is_some(),
            "Client was unexpectedly not refreshed: {ibc_events:?}"
        ),
        Ok(ibc_events) => assert!(
            ibc_events.is_none(),
            "Client was unexpectedly refreshed: {ibc_events:?}"
        ),
        Err(e) => panic!("Client refresh failed: {e:?}"),
    }
}
