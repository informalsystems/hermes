- Reduce the startup time of the relayer by querying the necessary
  information directly from the chain when one is configured with an
  allowlist, rather than scan for all clients, connections and channels
  ([#1536](https://github.com/informalsystems/ibc-rs/issues/1536))