Hermes v0.13.0 improves performance by lowering the pressure
on the full nodes by adding a caching layer for some queries.
It also fixes a bug which could cause an exponential slowdown
when relaying between many chains with a low average block time.

This release also add support for wildcards in port and channel identifiers
in the packet filter configuration, which enable operators to filter
ICA channels based on the port prefix.

Additionally, the IBC Protocol Buffers definitions can now be used from CosmWasm.

## Note for operators

To enable or disable relaying on [Interchain Accounts][ica] channels,
please check out the [new section in the guide][guide-ica].

[ica]: https://github.com/cosmos/ibc/blob/master/spec/app/ics-027-interchain-accounts/README.md
[guide-ica]: https://hermes.informal.systems/config.html#support-for-interchain-accounts
