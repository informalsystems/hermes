use ibc_relayer::{
    channel::version::Version,
    config::ChainConfig,
};
use ibc_test_framework::{
    chain::{
        config::{
            set_max_deposit_period,
            set_voting_period,
        },
        ext::{
            async_icq::AsyncIcqMethodsExt,
            bootstrap::ChainBootstrapMethodsExt,
        },
    },
    prelude::*,
    relayer::channel::{
        assert_eventually_channel_established,
        init_channel_version,
    },
    util::proposal_status::ProposalStatus,
};
use tendermint::abci::Event;
use tendermint_rpc::{
    Client,
    HttpClient,
};

#[test]
fn test_async_icq() -> Result<(), Error> {
    run_binary_connection_test(&AsyncIcqTest)
}

const MAX_DEPOSIT_PERIOD: &str = "10s";
const VOTING_PERIOD: u64 = 10;
const MAX_RETRIES: usize = 10;

pub struct AsyncIcqTest;

impl TestOverrides for AsyncIcqTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        config.mode.channels.enabled = true;
        config.mode.clients.misbehaviour = false;
    }

    // Allow Oracle message on host side
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        use serde_json::Value;

        set_max_deposit_period(genesis, MAX_DEPOSIT_PERIOD)?;
        set_voting_period(genesis, VOTING_PERIOD)?;

        let allow_messages = genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get_mut("interchainquery"))
            .and_then(|ica| ica.get_mut("params"))
            .and_then(|params| params.get_mut("allow_queries"))
            .and_then(|allow_messages| allow_messages.as_array_mut());

        if let Some(allow_messages) = allow_messages {
            allow_messages.push(Value::String(
                "/provenance.oracle.v1.Query/Oracle".to_string(),
            ));
            Ok(())
        } else {
            Err(Error::generic(eyre!("failed to update genesis file")))
        }
    }

    fn channel_version(&self) -> Version {
        Version::new("icq-1".to_owned())
    }
}

impl BinaryConnectionTest for AsyncIcqTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let fee_denom_a: MonoTagged<ChainA, Denom> =
            MonoTagged::new(Denom::base(&config.native_tokens[0]));
        let port_a = DualTagged::new(PortId::oracle());
        let port_b = DualTagged::new(PortId::icqhost());
        let (channel_id_b, channel_id_a) = init_channel_version(
            &chains.handle_a,
            &chains.handle_b,
            &chains.client_id_a(),
            &chains.client_id_b(),
            &connection.connection_id_a.as_ref(),
            &connection.connection_id_b.as_ref(),
            &port_a.as_ref(),
            &port_b.as_ref(),
            Version::new("icq-1".to_owned()),
        )?;

        // Check that the oracle channel is eventually established
        let _counterparty_channel_id = assert_eventually_channel_established(
            chains.handle_b(),
            chains.handle_a(),
            &channel_id_b.as_ref(),
            &port_b.as_ref(),
        )?;

        let driver = chains.node_a.chain_driver();

        let wallet_a = chains.node_a.wallets().user1().cloned();

        let relayer_a = chains.node_a.wallets().relayer().cloned();

        driver.update_oracle(
            &relayer_a.address().to_string(),
            &wallet_a.address().to_string(),
        )?;

        driver.value().assert_proposal_status(
            driver.value().chain_id.as_str(),
            &driver.value().command_path,
            &driver.value().home_path,
            &driver.value().rpc_listen_address(),
            ProposalStatus::VotingPeriod,
            "1",
        )?;

        driver.vote_proposal(&fee_denom_a.with_amount(381000000u64).to_string())?;

        info!("Assert that the update oracle proposal is eventually passed");

        driver.value().assert_proposal_status(
            driver.value().chain_id.as_str(),
            &driver.value().command_path,
            &driver.value().home_path,
            &driver.value().rpc_listen_address(),
            ProposalStatus::Passed,
            "1",
        )?;

        let query = r#"{"query_version":{}}"#;
        chains.node_a.chain_driver().async_icq(
            channel_id_a.a_side.channel_id().unwrap(),
            query,
            &wallet_a.address().to_string(),
        )?;

        assert_eventual_async_icq_success(&chains, &relayer)?;

        Ok(())
    }
}

/// Listen to events on the controller side to assert if the async ICQ is eventually
/// successful
fn assert_eventual_async_icq_success<ChainA: ChainHandle, ChainB: ChainHandle>(
    chains: &ConnectedChains<ChainA, ChainB>,
    relayer: &RelayerDriver,
) -> Result<(), Error> {
    let rpc_addr = match relayer.config.chains.first().unwrap() {
        ChainConfig::CosmosSdk(c) => c.rpc_addr.clone(),
    };

    let mut rpc_client = HttpClient::new(rpc_addr).unwrap();
    rpc_client.set_compat_mode(tendermint_rpc::client::CompatMode::V0_34);

    for _ in 0..MAX_RETRIES {
        if check_events(chains, &rpc_client).is_ok() {
            return Ok(());
        }
        sleep(Duration::from_secs(1));
    }

    Err(Error::generic(eyre!(
        "failed to find EventOracleQueryError or EventOracleQuerySuccess after {MAX_RETRIES} tries"
    )))
}

/// Checks if there is an Oracle event in the given events
fn check_events<ChainA: ChainHandle, ChainB: ChainHandle>(
    chains: &ConnectedChains<ChainA, ChainB>,
    rpc_client: &HttpClient,
) -> Result<(), Error> {
    let response = chains
        .node_a
        .chain_driver()
        .value()
        .runtime
        .block_on(rpc_client.latest_block_results())
        .map_err(|err| Error::generic(eyre!("Failed to fetch block results: {}", err)))?;

    if let Some(txs_results) = response.txs_results {
        if let Some(events) = txs_results
            .iter()
            .find_map(|v| find_oracle_event(&v.events))
        {
            return assert_async_icq_success(events);
        }
    }

    Err(Error::generic(eyre!(
        "No EventOracleQueryError or EventOracleQuerySuccess"
    )))
}

/// This method is used to find the Oracle event triggered by relaying
/// the acknowledgment of the async ICQ
fn find_oracle_event(event: &[Event]) -> Option<Event> {
    event
        .iter()
        .find(|&e| e.kind.contains("provenance.oracle.v1.EventOracleQuery"))
        .cloned()
}

/// This method is used to assert if the found Oracle event is successful or not
fn assert_async_icq_success(event: Event) -> Result<(), Error> {
    if event.kind == "provenance.oracle.v1.EventOracleQuerySuccess" {
        debug!("async query successful with event: {event:#?}");
        Ok(())
    } else {
        Err(Error::generic(eyre!(
            "async query failed with response event: {event:#?}"
        )))
    }
}
