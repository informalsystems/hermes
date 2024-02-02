*January 23rd, 2024*

This v1.8.0 release introduces new features and improvements to Hermes.

One key feature is that Hermes is now compatible with both the legacy `UpgradeProposal` and the newer `MsgIbcSoftwareUpgrade` message when upgrading a chain.
This allows Hermes to be compatible with ibc-go v8.0.0. The compatibility check that Hermes performs on startup has been updated to reflect this.

Additional configuration settings have been added:

- The new global settings `ics20_max_memo_size` and `ics20_max_receiver_size` allow users to specify a limit for the size of the memo and receiver fields for ICS20 packets. Any packet with either field having a size exceeding the configured values will not be relayed.
- The new per-chain setting `query_packets_chunk_size` allows users to specify how many packets are queried at once from the chain when clearing pending packets. This is useful to tweak when there are many large pending packets and the RPC endpoints times out or refuses to answer the pending packets query.
- The new per-chain setting `client_refresh_rate` can be use to specify how often the clients referencing this chain should be refreshed. The rate is expressed as a fraction of the trusting period.
- The new per-chain setting `dynamic_gas_price` can be enabled to have the relayer query for and use a dynamic gas price instead of using the static `gas_price` specified in the config. This should only be used for chains which have a [EIP-1559][eip-1559]-like fee market enabled and support the `osmosis.txfees.v1beta1.Query/GetEipBaseFee` gRPC query.

Telemetry now features new metrics:
- Monitoring the ICS20 packets filtered due to the memo and/or receiver field size exceeding the configured limits.
- Monitoring the distribution of dynamic gas fees queried from the chain, if enabled.

[eip-1559]: https://metamask.io/1559/
