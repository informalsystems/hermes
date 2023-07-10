# Handling Clock Drift

IBC light client security model requires that the timestamp of a header included in client updates for some `client` is within `[now - client.trusting_period, now + client.max_clock_drift)`.

The `trusting_period` is a parameter that is configurable under the `[[chains]]` section and its default value is two thirds of the chain `unbonding_period`.
The rest of this section describes the configuration parameters that determine the `max_clock_drift`.

IBC light client security model requires that the clocks of the reference and host chains are roughly synchronized. Hermes uses the `clock_drift` and `max_block_time` configuration parameters to determine how much clock drift is tolerable between the reference and host chains.
 - `clock_drift` is a correction parameter that specifies how far in the future or past a chain's clock may be from the current time..
 - `max_block_time` is the maximum amount of time that can occur before a new block is created on the chain. 

> **Note:** For Cosmos SDK chains, a good approximation for `max_block_time` is `C * (timeout_propose + timeout_commit)`,
where `C` is a constant to allow for variation in block times, mainly due to tx execution time which is outside of 
consensus params. To allow for some variance in block times while still detecting [forward lunatic attacks][forward-lunatic], 
it is recommended to set `C` to be in the `3..5` range. Hermes uses the default value of `30s` which is a good approximation 
for most Cosmos SDK chains that have 6-10sec block times.

The `clock_drift` parameter values on both the reference and host chains, and `max_block_time` of the host chain are summed to get the `max_clock_drift` when creating a client on the host chain.
This can be summarized more succinctly in the following equation: 
```
client.max_clock_drift = reference.clock_drift + host.max_block_time + host.clock_drift
```

Thus, when configuring these values in Hermes' `config.toml`, keep in mind that this is how these 
parameters will be used. If the total clock drift is too small, then we run the risk of client
updates being rejected because a new block won't have been created yet. It's better to err on the
side of total clock drift being larger than smaller, however, if this value ends up being _too_
large, then this becomes a security vulnerability.

For a more concrete example of what could happen when clock drift is mis-configured, take a look
at the [Mishandling Clock Drift][mishandling-clock-drift] troubleshooting section.

[forward-lunatic]: https://github.com/cometbft/cometbft/blob/main/docs/architecture/tendermint-core/adr-047-handling-evidence-from-light-client.md#appendix-b
[mishandling-clock-drift]: ./cross-comp-config.md#mishandling-clock-drift