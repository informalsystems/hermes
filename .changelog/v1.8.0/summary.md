*January 22nd, 2024*

This v1.8.0 release introduces new features and improvements to Hermes.

One key feature is that Hermes is now compatible with both the legacy UpgradeProposal and the newer MsgIbcSoftwareUpgrade message when upgrading a chain. This allows Hermes to be compatible with ibc-go v8.0.0.
Compatibility check has been updated to reflect the new versions.

Additional configuration has been added:
The configurations ics20_max_memo_size and ics20_max_receiver_size allow users to specify a limit for the memo and receiver field size for ICS20 packets. Any packet with one or both fields higher than the configured values will not be relayed.
- The new configuration `query_packets_chunk_size allows users to specify how many packets are queried at once when clearing pending packets.
- The new configuration `client_refresh_rate` can be set per-chain to specify how often the clients referencing this chain should be refreshed.
- The new configuration `dynamic_gas_price` can be enabled to have the relayer query and use the dynamic gas price instead of using the static gas price. This should only be used for chains which have [EIP-1559][eip]-like dynamic gas price.
Please note that the chain configurations now take different types of chains, with the default being CosmosSdk.

The telemetry has new metrics allowing:
- Monitoring the ICS20 packets filtered due to the memo and/or receiver field size
- Monitoring the dynamic gas fees queried and used if it is enabled

[eip]: https://metamask.io/1559/