use std::time::Duration;

use ibc_relayer::chain::requests::{
    PageRequest,
    QueryConsensusStateHeightsRequest, // QueryConsensusStatesRequest,
};

use ibc_test_framework::prelude::*;

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
            eprintln!("updating client ({i}/{UPDATES_COUNT})...");

            client.update().map_err(Error::foreign_client)?;

            if i != UPDATES_COUNT {
                std::thread::sleep(Duration::from_secs(5));
            }
        }

        // let states = chains
        //     .handle_b()
        //     .query_consensus_states(QueryConsensusStatesRequest {
        //         client_id: (*chains.client_id_b().value()).clone(),
        //         pagination: Some(PageRequest::all()),
        //     })?;

        // assert_eq!(states.len(), CONSENSUS_STATES_COUNT);

        let heights =
            chains
                .handle_b()
                .query_consensus_state_heights(QueryConsensusStateHeightsRequest {
                    client_id: (*chains.client_id_b().value()).clone(),
                    pagination: Some(PageRequest::all()),
                })?;

        assert_eq!(heights.len(), CONSENSUS_STATES_COUNT);

        // states
        //     .into_iter()
        //     .zip(heights.into_iter())
        //     .for_each(|(state, height)| {
        //         assert_eq!(state.height, height);
        //     });

        Ok(())
    }
}
