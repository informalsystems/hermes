use std::time::Duration;

use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;

use ibc_relayer::chain::requests::{IncludeProof, QueryClientStateRequest, QueryHeight};
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::foreign_client::CreateOptions;
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState as TmClientState;

use ibc_test_framework::prelude::*;

/// A test to exercise default foreign client settings.
#[test]
fn test_client_defaults() -> Result<(), Error> {
    run_binary_chain_test(&ClientDefaultsTest)
}

/// A test to exercise customization of foreign client settings.
#[test]
fn test_client_options() -> Result<(), Error> {
    run_binary_chain_test(&ClientOptionsTest)
}

struct ClientDefaultsTest;

struct ClientOptionsTest;

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
        let client_id = chains.foreign_clients.client_a_to_b.id();
        let state = query_client_state(chains.handle_b, client_id)?;
        assert_eq!(state.max_clock_drift, Duration::from_secs(24));
        assert_eq!(state.trusting_period, Duration::from_secs(120_000));
        assert_eq!(state.trust_threshold, TrustThreshold::new(13, 23).unwrap());

        let client_id = chains.foreign_clients.client_b_to_a.id();
        let state = query_client_state(chains.handle_a, client_id)?;
        assert_eq!(state.max_clock_drift, Duration::from_secs(14));
        assert_eq!(state.trusting_period, Duration::from_secs(340_000));
        assert_eq!(state.trust_threshold, TrustThreshold::TWO_THIRDS);
        Ok(())
    }
}

impl TestOverrides for ClientOptionsTest {
    fn client_options_a_to_b(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(3)),
            trusting_period: Some(Duration::from_secs(120_000)),
            trust_threshold: Some(TrustThreshold::new(13, 23).unwrap()),
        }
    }

    fn client_options_b_to_a(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(6)),
            trusting_period: Some(Duration::from_secs(340_000)),
            trust_threshold: Some(TrustThreshold::TWO_THIRDS),
        }
    }
}

impl BinaryChainTest for ClientOptionsTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let client_id = chains.foreign_clients.client_a_to_b.id();
        let state = query_client_state(chains.handle_b, client_id)?;
        assert_eq!(state.max_clock_drift, Duration::from_secs(3));
        assert_eq!(state.trusting_period, Duration::from_secs(120_000));
        assert_eq!(state.trust_threshold, TrustThreshold::new(13, 23).unwrap());

        let client_id = chains.foreign_clients.client_b_to_a.id();
        let state = query_client_state(chains.handle_a, client_id)?;
        assert_eq!(state.max_clock_drift, Duration::from_secs(6));
        assert_eq!(state.trusting_period, Duration::from_secs(340_000));
        assert_eq!(state.trust_threshold, TrustThreshold::TWO_THIRDS);
        Ok(())
    }
}

fn query_client_state<Chain: ChainHandle>(
    handle: Chain,
    id: &ClientId,
) -> Result<TmClientState, Error> {
    let (state, _) = handle.query_client_state(
        QueryClientStateRequest {
            client_id: id.clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;
    #[allow(unreachable_patterns)]
    match state {
        AnyClientState::Tendermint(state) => Ok(state),
        _ => unreachable!("unexpected client state type"),
    }
}
