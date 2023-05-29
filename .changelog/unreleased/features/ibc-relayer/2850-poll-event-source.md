- Add a poll-based event source which fetches events from the chain using
  the `/block_results` RPC endpoint instead of getting them over WebSocket.

  To use the poll-based event source, set `event_source = 'poll'` in the per-chain configuration.

  **Warning**
  Only use this if you think Hermes is not getting all
  the events it should, eg. when relaying for a CosmWasm-enabled blockchain
  which emits IBC events in a smart contract where the events lack the
  `message` attribute key. See #3190 and #2809 for more background information.

  ([\#2850](https://github.com/informalsystems/hermes/issues/2850))
