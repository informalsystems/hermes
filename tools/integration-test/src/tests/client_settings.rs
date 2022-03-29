use std::time::Duration;

use tendermint::trust_threshold::TrustThresholdFraction;

use ibc::core::ics02_client::client_state::AnyClientState;
use ibc::Height;
use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::cosmos;

use ibc_test_framework::prelude::*;
use ibc_test_framework::relayer::refresh::spawn_refresh_client_tasks;

/// A test to exercise customization of foreign client settings.
#[test]
fn test_client_settings() -> Result<(), Error> {
    run_binary_chain_test(&ClientSettingsTest)
}

struct ClientSettingsTest;

struct SettingsTestOverrides;

impl TestOverrides for SettingsTestOverrides {
    fn client_settings_a_to_b(&self) -> ClientSettings {
        ClientSettings::Cosmos(cosmos::client::Settings {
            max_clock_drift: Some(Duration::from_secs(3)),
            trusting_period: Some(Duration::from_secs(120_000)),
            trust_threshold: Some(TrustThresholdFraction::new(13, 23).unwrap()),
        })
    }

    fn client_settings_b_to_a(&self) -> ClientSettings {
        ClientSettings::Cosmos(cosmos::client::Settings {
            max_clock_drift: Some(Duration::from_secs(6)),
            trusting_period: Some(Duration::from_secs(340_000)),
            trust_threshold: Some(TrustThresholdFraction::new(17, 29).unwrap()),
        })
    }
}

impl BinaryChainTest for ClientSettingsTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let _refresh_tasks = spawn_refresh_client_tasks(&chains.foreign_clients)?;
        let _supervisor = relayer.spawn_supervisor()?;
        let state = chains
            .handle_a
            .query_client_state(chains.foreign_clients.client_a_to_b.id(), Height::zero())?;
        let state = match state {
            AnyClientState::Tendermint(s) => s,
            _ => unreachable!("unexpected client state type"),
        };
        assert_eq!(state.max_clock_drift, Duration::from_secs(3));
        Ok(())
    }
}

impl HasOverrides for ClientSettingsTest {
    type Overrides = SettingsTestOverrides;

    fn get_overrides(&self) -> &SettingsTestOverrides {
        &SettingsTestOverrides
    }
}
