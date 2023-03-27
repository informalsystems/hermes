Hermes v1.4.0 brings compatibility with chains based on Tendermint/CometBFT 0.37,
while retaining compatiblity with Tendermint/CometBFT 0.34. This is transparent
and does not require any additional configuration.

The relayer now supports ICS consumer chains, which only requires operators
to specify the `unbonding_period` parameter in the chain settings. This is only
a temporary requirement, in the future Hermes will seamlessy support consumer
chains with minimal changes to the configuration.

This release also deprecates support for chains based on Cosmos SDK 0.43.x and lower,
and bumps the compatiblity to Cosmos SDK 0.47.x.

The relayer now also allows operators to filter out packets to relay based on whether
or not they contain a fee, and the minimal amount of such fee.
Please check the relevant [documentation in the Hermes guide](fee-guide) for more information.
Additionnaly, Hermes now also tracks [metrics for ICS29 fees](fee-metrics).

This release includes a new `query client status` CLI to quickly check whether a client is active, expired or frozen.

[fee-guide]: https://hermes.informal.systems/documentation/configuration/filter-incentivized.html
[fee-metrics]: https://hermes.informal.systems/documentation/telemetry/operators.html#am-i-getting-fee-rewards

