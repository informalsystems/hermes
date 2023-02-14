*March 28th, 2022*

Hermes v0.13.0 improves performance by lowering the pressure
on the full nodes by adding a caching layer for some queries.
It also fixes a bug which could cause an exponential slowdown
when relaying between many chains with a low average block time.

This release also add support for wildcards in port and channel identifiers
in the packet filter configuration, which enable operators to filter
ICA channels based on the port prefix.

Additionally, the IBC Protocol Buffers definitions can now be used from CosmWasm.

## Note for operators

As of version 0.13.0, Hermes supports relaying on [Interchain Accounts][ica] channels.

If the `packet_filter` option in the chain configuration is disabled, then
Hermes will relay on all existing and future channels, including ICA channels.

There are two kinds of ICA channels:

1. The host channels, whose port is `icahost`
2. The controller channels, whose port starts with `icacontroller-` followed
   by the owner account address. [See the spec for more details][ica].

If you wish to only relay on a few specific standard channels (here `channel-0` and `channel-1`),
but also relay on all ICA channels, you can specify the following packet filter:

> Note the use of wildcards in the port and channel identifiers (`['ica*', '*']`)
> to match over all the possible ICA ports.

```toml
[chains.packet_filter]
policy = 'allow'
list = [
  ['ica*', '*'], # allow relaying on all channels whose port starts with `ica`
  ['transfer', 'channel-0'],
  ['transfer', 'channel-1'],
  # Add any other port/channel pairs you wish to relay on
]
```

If you wish to relay on all channels but not on ICA channels, you can use
the following packet filter configuration:

```toml
[chains.packet_filter]
policy = 'deny'
list = [
  ['ica*', '*'], # deny relaying on all channels whose port starts with `ica`
]
```

This information can also be found in the [Hermes guide][guide-ica].

[ica]: https://github.com/cosmos/ibc/blob/master/spec/app/ics-027-interchain-accounts/README.md
[guide-ica]: https://hermes.informal.systems/documentation/configuration/configure-hermes.html#support-for-interchain-accounts

