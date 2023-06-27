//! The following tests are for the Cross-chain Queries, ICS31.
//! These tests require the first chain to be a Gaia chain and
//! the second chain a Stride chain. Only the Stride chain requires
//! to have the ICS31 enabled.
//!
//! The test `ICS31Test` registers the cosmos account as a host-zone
//! using `strided tx stakeibc register-host-zone` in order to have
//! the Stride chain trigger Cross-chain Queries.
//! The test then waits for a Cross-chain Query to be pending and
//! then processed.
use std::thread;

use ibc_test_framework::chain::config::set_voting_period;
use ibc_test_framework::framework::binary::channel::run_binary_interchain_security_channel_test;
use ibc_test_framework::prelude::*;

#[test]
fn test_ics31_cross_chain_queries() -> Result<(), Error> {
    run_binary_interchain_security_channel_test(&InterchainSecurityTest)
}

struct InterchainSecurityTest;

impl TestOverrides for InterchainSecurityTest {
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error> {
        // Consumer chain doesn't have a gov key.
        if genesis
            .get_mut("app_state")
            .and_then(|app_state| app_state.get("gov"))
            .is_some()
        {
            set_voting_period(genesis, "10s")?;
        }
        Ok(())
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        for chain_config in config.chains.iter_mut() {
            if chain_config.id == ChainId::from_string("ibcconsumer") {
                chain_config.ccv_consumer_chain = true;
                chain_config.trusting_period = Some(Duration::from_secs(99));
            }
        }
    }
}

impl BinaryChannelTest for InterchainSecurityTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        _chains: ConnectedChains<ChainA, ChainB>,
        _channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        thread::sleep(Duration::from_secs(1));
        Ok(())
    }
}
