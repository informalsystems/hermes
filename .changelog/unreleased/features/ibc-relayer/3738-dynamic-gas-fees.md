- Add a new per-chain configuration table `dynamic_gas` which enables
  querying the current gas price from the chain instead of the static `gas_price`, 
  when the chain has [EIP-1559][eip]-like dynamic gas price. 
  New new configuration setting can be configured per-chain as follows:
  ```toml
  dynamic_gas = { enabled = true, gas_price_multiplier = 1.1, max_gas_price = 0.6 }
  ```
  At the moment, only chains which support the `osmosis.txfees.v1beta1.Query/GetEipBaseFee`
  query can be used with dynamic gas price enabled.
  ([\#3738](https://github.com/informalsystems/hermes/issues/3738))

[eip]: https://metamask.io/1559/
