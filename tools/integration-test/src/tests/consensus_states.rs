use ibc_relayer::{
    chain::{
        cosmos::query::consensus_state::query_consensus_states,
        requests::{PageRequest, QueryConsensusStateHeightsRequest, QueryConsensusStatesRequest},
    },
    config::ChainConfig,
};

use ibc_test_framework::prelude::*;
use ibc_test_framework::util::namada;

#[test]
fn test_consensus_state_heights() -> Result<(), Error> {
    run_binary_chain_test(&ConsensusStateHeights)
}

struct ConsensusStateHeights;

impl TestOverrides for ConsensusStateHeights {}

impl BinaryChainTest for ConsensusStateHeights {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        const UPDATES_COUNT: usize = 4;
        const CONSENSUS_STATES_COUNT: usize = UPDATES_COUNT + 1;

        let client = &chains.foreign_clients.client_a_to_b;

        for i in 1..=UPDATES_COUNT {
            client.update().map_err(Error::foreign_client)?;

            if i != UPDATES_COUNT {
                std::thread::sleep(Duration::from_secs(5));
            }
        }

        let heights =
            chains
                .handle_b()
                .query_consensus_state_heights(QueryConsensusStateHeightsRequest {
                    client_id: (*chains.client_id_b().value()).clone(),
                    pagination: Some(PageRequest::all()),
                })?;

        assert_eq(
            "did not find the expected amount of consensus state heights",
            &heights.len(),
            &CONSENSUS_STATES_COUNT,
        )?;

        let states = match chains.handle_b().config().expect("Config should exist") {
            ChainConfig::Namada(config) => chains.node_b.value().chain_driver.runtime.block_on(
                namada::query_consensus_states(
                    config
                        .rpc_addr
                        .to_string()
                        .parse()
                        .expect("RPC address should be converted"),
                    chains.client_id_b().value(),
                ),
            )?,
            _ => {
                let grpc_address = chains
                    .node_b
                    .value()
                    .chain_driver
                    .grpc_address()
                    .as_str()
                    .parse()
                    .unwrap();

                chains
                    .node_b
                    .value()
                    .chain_driver
                    .runtime
                    .block_on(query_consensus_states(
                        chains.node_b.chain_id().value(),
                        &grpc_address,
                        QueryConsensusStatesRequest {
                            client_id: (*chains.client_id_b().value()).clone(),
                            pagination: Some(PageRequest::all()),
                        },
                    ))?
            }
        };

        assert_eq(
            "did not find the expected number of consensus states",
            &states.len(),
            &CONSENSUS_STATES_COUNT,
        )?;

        states
            .into_iter()
            .zip(heights.into_iter())
            .try_for_each(|(state, height)| {
                assert_eq(
                    "did not find matching height for each consensus state",
                    &state.height,
                    &height,
                )
            })?;

        Ok(())
    }
}
