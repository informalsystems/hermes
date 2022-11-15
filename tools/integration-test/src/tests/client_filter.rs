//! This test ensures that the [`FilterPolicy`] type correctly filters clients
//! based on the clients' [`TrustThreshold`]. Clients with `TrustThreshold`
//! values less than 1/3 or greater than 2/3 should not be allowed. Note that
//! in order for a client to be allowed, _both_ client connections must
//! exhibit a `TrustThreshold` value within the acceptable range.
//!
//! `ClientFilterBlocksConnectionTest` sets the `TrustThreshold` for the client
//! outside of the acceptable range; the `TrustThreshold` of the client connection
//! from chain A to chain B is too large, though the `TrustThreshold` of the
//! client connection from chain B to chain A is within the acceptable range.
//! It then asserts that no client workers were established on account of the
//! connection not being allowed through.
//!
//! `ClientFilterAllowsConnectionTest` sets the `TrustThreshold` for the client
//! within the acceptable range in both directions such that the client connection
//! is allowed through the filter. It then asserts that client workers were
//! established as a result of the connection being allowed through.

use std::time::Duration;

use ibc_relayer::supervisor::client_state_filter::{FilterPolicy, Permission};
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;

use ibc_relayer::chain::requests::{IncludeProof, QueryClientStateRequest, QueryHeight};
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::foreign_client::CreateOptions;
use ibc_relayer::object::ObjectType;
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState as TmClientState;

use ibc_test_framework::prelude::*;

struct ClientFilterBlocksConnectionTest;
struct ClientFilterAllowsConnectionTest;

#[test]
fn test_client_filter_blocks_connection() -> Result<(), Error> {
    run_binary_channel_test(&ClientFilterBlocksConnectionTest)
}

#[test]
fn test_client_filter_allows_connection() -> Result<(), Error> {
    run_binary_channel_test(&ClientFilterAllowsConnectionTest)
}

impl TestOverrides for ClientFilterBlocksConnectionTest {
    fn client_options_a_to_b(&self) -> CreateOptions {
        CreateOptions {
            max_clock_drift: Some(Duration::from_secs(3)),
            trusting_period: Some(Duration::from_secs(120_000)),
            trust_threshold: Some(TrustThreshold::new(20, 23).unwrap()),
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

impl TestOverrides for ClientFilterAllowsConnectionTest {
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
            trust_threshold: Some(TrustThreshold::ONE_THIRD),
        }
    }
}

impl BinaryChannelTest for ClientFilterBlocksConnectionTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        _channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let mut policy = FilterPolicy::default();

        let client_id = chains.foreign_clients.client_a_to_b.id();
        let chain_id = chains.handle_b.id();
        let state = query_client_state(chains.handle_b, client_id)?;
        let state = AnyClientState::Tendermint(state);
        assert_eq!(
            policy.control_client(&chain_id, client_id, &state),
            Permission::Deny
        );

        let client_id = chains.foreign_clients.client_b_to_a.id();
        let chain_id = chains.handle_a.id();
        let state = query_client_state(chains.handle_a, client_id)?;
        let state = AnyClientState::Tendermint(state);
        assert_eq!(
            policy.control_client(&chain_id, client_id, &state),
            Permission::Allow
        );

        let supervisor = relayer.spawn_supervisor()?;
        let state = supervisor.dump_state()?;

        assert!(!state.workers.contains_key(&ObjectType::Client));

        Ok(())
    }
}

impl BinaryChannelTest for ClientFilterAllowsConnectionTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        _channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let mut policy = FilterPolicy::default();

        let client_id = chains.foreign_clients.client_a_to_b.id();
        let chain_id = chains.handle_b.id();
        let state = query_client_state(chains.handle_b, client_id)?;
        let state = AnyClientState::Tendermint(state);
        assert_eq!(
            policy.control_client(&chain_id, client_id, &state),
            Permission::Allow
        );

        let client_id = chains.foreign_clients.client_b_to_a.id();
        let chain_id = chains.handle_a.id();
        let state = query_client_state(chains.handle_a, client_id)?;
        let state = AnyClientState::Tendermint(state);
        assert_eq!(
            policy.control_client(&chain_id, client_id, &state),
            Permission::Allow
        );

        let supervisor = relayer.spawn_supervisor()?;
        let state = supervisor.dump_state()?;

        assert!(state.workers.contains_key(&ObjectType::Client));

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
