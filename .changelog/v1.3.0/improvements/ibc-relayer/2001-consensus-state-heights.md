- Fetch consensus state heights using the more efficient
  `QueryConsensusStateHeights` gRPC query instead of fetching all the consensus
  states themselves using `QueryConsensusStates` and extracting the heights from
  the result. ([#2001](https://github.com/informalsystems/ibc-rs/issues/2001))