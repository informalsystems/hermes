# Dynamic Gas Fees

Some chains use a dynamic gas price system instead of static gas price. By configuring the `dynamic_gas_price` for those chains, Hermes will query the gas price and apply the configured multiplier instead of using the configured static gas price:

```toml
...
[<chain_id>.dynamic_gas_price]
enabled = true
multiplier = 1.1
max = 0.6
...
```

## Notes

* If the query fails, Hermes will fallback to the configured static gas price.
* If the queried gas price is higher than the maximum configured gas price, Hermes will use the maximum gas price but this might cause the relaying of the packet to fail due to insufficient fees.

## Monitoring

As this feature can be delicate to handle, multiple metrics have been added in order to monitor the dynamic gas fees. Please consult the [Dynamic Gas Metrics](../telemetry/operators.md#dynamic-gas-fees)  section for detailed information on these metrics.