- Add a new `trusted_node` setting to the per-chain configuration to
  specify whether or not the full node Hermes connects to is trusted.
  If not trusted (ie. `trusted_node = false`), Hermes will verify headers
  included in the `ClientUpdate` message using the light client.

  If the full node is configured as trusted then, in addition to headers not being verified,
  the verification traces will not be provided.
  This may cause failure in client updates after significant change in validator sets.

  > **Warning**
  > Setting this flag to `true` may reduce latency but at the expense of
  > potentially sending invalid client updates to the chain, only use
  > when latency is more critical than operating costs. Use at your own risk.

  ([\#3330](https://github.com/informalsystems/hermes/issues/3330))
