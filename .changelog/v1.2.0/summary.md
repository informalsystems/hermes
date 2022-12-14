Hermes v1.2.0 brings a bunch of new features and other improvements, such as
support for Ed25519 keys, more robust health check which takes into account
the Tendermint `min_gas_price` setting, and various bug fixes related to
the handling of begin- and end-block events in the Tendermint indexer.

Additionally, IBC clients with a trust level between `1/3` and `2/3` inclusive are now allowed.
