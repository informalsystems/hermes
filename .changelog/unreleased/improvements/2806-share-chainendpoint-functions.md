- Move default implementations of `init_event_monitor`, `id`, `get_key`,
  and `add_key` from CosmosSdkChain to ChainEndpoint, and change
  `ChainEndpoint::config()` to return a `&ChainConfig` instead of
  a `ChainConfig`. ([#2806](https://github.com/informalsystems/ibc-rs/issues/2806))