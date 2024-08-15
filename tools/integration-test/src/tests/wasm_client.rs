use core::time::Duration;
use std::path::PathBuf;
use std::thread::sleep;

use ibc_test_framework::bootstrap::binary::channel::bootstrap_channel;
use ibc_test_framework::bootstrap::binary::connection::bootstrap_connection;
use sha2::Digest;

use ibc_relayer::foreign_client::{
    CreateOptions, ForeignClientError, TendermintCreateOptions, WasmCreateOptions,
};
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::events::IbcEvent;
use ibc_test_framework::bootstrap::binary::chain::{
    add_chain_config, bootstrap_foreign_client, new_registry, save_relayer_config,
    spawn_chain_handle,
};
use ibc_test_framework::chain::config::{
    add_allowed_client, set_max_body_bytes, set_max_deposit_period, set_voting_period,
};
use ibc_test_framework::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use ibc_test_framework::chain::ext::wasm_client::StoreWasmClientCodeMethodsExt;
use ibc_test_framework::prelude::*;
use ibc_test_framework::types::binary::chains::DropChainHandle;
use ibc_test_framework::types::env::write_env;
use ibc_test_framework::util::proposal_status::ProposalStatus;

#[test]
fn test_create_and_update_wasm_client() -> Result<(), Error> {
    run_binary_node_test(&CreateAndUpdateWasmClientTest)
}

const WASM_PATH_ENV: &str = "IBC_CLIENT_WASM_FILE";

fn ibc_client_wasm_path() -> PathBuf {
    PathBuf::from(std::env::var(WASM_PATH_ENV).expect("IBC_CLIENT_WASM_FILE not set"))
}

fn ibc_client_wasm_code() -> Vec<u8> {
    std::fs::read(ibc_client_wasm_path()).expect("failed to read Wasm code")
}

const TM_CREATE_OPTIONS: TendermintCreateOptions = TendermintCreateOptions {
    max_clock_drift: Some(Duration::from_secs(3)),
    trusting_period: Some(Duration::from_secs(120)),
    trust_threshold: Some(TrustThreshold::TWO_THIRDS),
};

fn wasm_options() -> CreateOptions {
    let checksum = sha2::Sha256::digest(ibc_client_wasm_code());

    WasmCreateOptions {
        checksum: checksum.to_vec(),
        underlying: TM_CREATE_OPTIONS.into(),
    }
    .into()
}

struct CreateAndUpdateWasmClientTest;

impl TestOverrides for CreateAndUpdateWasmClientTest {
    fn client_options_b_to_a(&self) -> CreateOptions {
        wasm_options()
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }

    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        set_max_deposit_period(genesis, "10s")?;
        set_voting_period(genesis, 10)?;
        add_allowed_client(genesis, "08-wasm")?;

        Ok(())
    }

    fn modify_node_config(&self, config: &mut toml::Value) -> Result<(), Error> {
        set_max_body_bytes(config, 10001048576)?;

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

        let overrides = self.get_overrides();

        info!("Creating client A to B");
        let mut client_a_to_b =
            bootstrap_foreign_client(&chain_a, &chain_b, overrides.client_options_a_to_b())?;

        info!("Creating client B to A");
        let mut client_b_to_a =
            bootstrap_foreign_client(&chain_b, &chain_a, overrides.client_options_b_to_a())?;

        info!("Refreshing client A to B...");
        let res = client_a_to_b.force_refresh();

        assert_client_refreshed(true, res);
        info!("Client A to B was refreshed successfully");

        info!("Refreshing client B to A...");
        let res = client_b_to_a.force_refresh();

        assert_client_refreshed(true, res);
        info!("Client B to A was refreshed successfully");

        let foreign_clients = ForeignClientPair::new(client_a_to_b.clone(), client_b_to_a.clone());

        bootstrap_connection(&foreign_clients, Default::default())?;
        let port_a = DualTagged::new(PortId::transfer());
        let port_b = DualTagged::new(PortId::transfer());

        let _ = client_a_to_b.force_refresh();
        let _ = client_b_to_a.force_refresh();

        bootstrap_channel(
            &foreign_clients,
            &port_a.as_ref(),
            &port_b.as_ref(),
            Default::default(),
            Default::default(),
        )?;

        Ok(())
    }
}

fn store_wasm_contract(node_a: FullNode, test_config: &TestConfig) -> Result<(), Error> {
    let fee_denom_a = test_config.native_token(0);
    node_a.chain_driver.store_wasm_client_code(
        &ibc_client_wasm_path(),
        "tmp",
        "tmp",
        "validator",
    )?;

    node_a
        .chain_driver
        .assert_proposal_status(ProposalStatus::DepositPeriod, "1")?;

    node_a.chain_driver.deposit_proposal(
        &format!("381000000{}", fee_denom_a),
        "1",
        &format!("381000000{}", fee_denom_a),
        "100000",
    )?;

    node_a
        .chain_driver
        .assert_proposal_status(ProposalStatus::VotingPeriod, "1")?;

    node_a
        .chain_driver
        .vote_proposal(&format!("381000000{}", fee_denom_a), "1")?;

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
