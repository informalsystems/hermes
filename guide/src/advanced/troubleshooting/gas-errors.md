# Gas errors

This section will expand on the out of gas error which can happen when simulating or sending Txs. The related configurations are:

```toml
default_gas = 100000
max_gas = 4000000
gas_multiplier = 1.1
```

Before sending a transaction, Hermes will retrieve an estimation of the gas required with the simulation capability of the chain. After retrieving the gas amount from the simulation, the `gas_multiplier` will be applied since the simulation might be slightly lower than the required amount of gas.
Since the `max_gas` is applied after the gas_multiplier, it can happen that the value `simulated_gas * gas_multiplier > max_gas`, in which case the `max_gas` value is used.

Note that if the simulation fails with a recoverable error, Hermes will use the configured `default_gas`.

## Simulating Tx

The first instance where an error can happen is when the tracasction simulation succeeds but the gas amount retrieved exceeds the configured `max_gas`, Hermes will throw an unrecoverable error:

```
<chain> gas estimate <simulated_gas> from simulated Tx exceeds the maximum configured <max_gas>
```

This can be fixed by increasing the configured `max_gas`.

## Broadcasting Tx

> __NOTE__: This issue will only arise with Cosmos chains as this is a Cosmos SDK error.

The second instance when an error can happen is when sending the transaction. If the gas included for the transaction is not enough Hermes will throw an error:

```
out of gas in location: <location>; gasWanted: <max gas Hermes>, gasUsed: <gas wanted>: out of gas
```

Two cases need to be verified in order to fix this issue.

### Caused by max_gas

If simulated gas is close to the `max_gas` configured, after multiplying the value with the `gas_multiplier`, it can be the case that the `max_gas` is used instead. And since the simulated gas might be slightly lower than the required gas, this can cause an out of gas error.
This can be fixed by increasing the configured `max_gas`.

### Caused by default_gas

When the transaction simulation fails with a recoverable error, the `default_gas` will be used. If the `default_gas` is too low an out of gas error will be thrown. This can be fixed by increasing the `default_gas`.
But there can also be a case similar to the one explained in the previous section [Caused by max_gas](./gas-errors.md#caused-by-max_gas).

If the `default_gas` is too close to the `max_gas`, the `max_gas` will be used instead of `default_gas * gas_multiplier`, causing an out of gas error. In this situation both `max_gas` and `default_gas` need to be verified, and one or both need to be increased.