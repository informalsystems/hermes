# Handling Clock Drift

When it comes to distributed systems, clock drift is always a consideration that needs to be 
taken into account. There is always some amount of drift between the clock of the source chain 
and the clock of the destination chain that must be accounted for. As far as Hermes is concerned,
there are two configuration parameters that exist to specify how much clock drift ought to be tolerated: 
 - `clock_drift` is a correction parameter that specifies how far in the future or past a chain's clock may
   drift in relation to this client. The destination chain for this client uses this parameter when deciding
	 whether to accept or reject a new header from the source chain for this client.
 - `max_block_time` is the maximum amount of time that can occur before a new block is created on the chain. 

> **Note:** When it comes to Cosmos SDK chains, a good approximation for `max_block_time` is
`timeout_propose` + `timeout_commit`, which together sum up to the total amount of time before
the proposal and commitment steps for a new block time out. 

`max_block_time` and the `clock_drift` parameter values on both the source and destination chains 
are summed to get the `total_clock_drift` that is tolerable when creating a client on this chain. 
This can be summarized more succinctly in the following equation: 
```
total_clock_drift = max_block_time + source_clock_drift + destination_clock_drift
```

Thus, when configuring these values in Hermes' `config.toml`, keep in mind that this is how these 
parameters will be used. If the total clock drift is too small, then we run the risk of client
updates being rejected because a new block won't have been created yet. It's better to err on the
side of total clock drift being larger than smaller, however, if this value ends up being _too_
large, then this becomes a security vulnerability.

For a more concrete example of what could happen when clock drift is mis-configured, take a look
at the [Mishandling Clock Drift][mishandling-clock-drift] troubleshooting section.

[mishandling-clock-drift]: ./cross-comp-config.md#mishandling-clock-drift