- Refactor the `ChainEndpoint` trait to expose the light client
  functionality directly. Instead of exposing a getter for the
  `LightClient` trait, the `ChainEndpoint` trait now defines the
  two methods `verify_header` and `check_misbehaviour` directly.
  ([#2548](https://github.com/informalsystems/ibc-rs/issues/2548))