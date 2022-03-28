# CHANGELOG

## v0.13.0
*March 28th, 2022*

Hermes v0.13.0 improves performance by lowering the pressure
on the full nodes by adding a caching layer for some queries.
It also fixes a bug which could cause an exponential slowdown
when relaying between many chains with a low average block time.

This release also add support for wildcards in port and channel identifiers
in the packet filter configuration, which enable operators to filter
ICA channels based on the port prefix.

Additionally, the IBC Protocol Buffers definitions can now be used from CosmWasm.

### Note for operators

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
[guide-ica]: https://hermes.informal.systems/config.html#support-for-interchain-accounts

### BUG FIXES

- [Relayer Library](relayer)
  - Fixed relayer behavior on ordered channels
    ([#1835](https://github.com/informalsystems/ibc-rs/issues/1835))
  - Do not spawn packet worker on chan open ack/confirm events
    ([#1991](https://github.com/informalsystems/ibc-rs/issues/1991))
  - Fix a bug which would cause the relayer to slow down exponentially when either
    the average block time was low or when it was relaying on too many chains at
    once ([#2008](https://github.com/informalsystems/ibc-rs/issues/2008))

### FEATURES

- [IBC Proto](proto)
  - Add CosmWasm support to the generated Protobuf code ([#1913](https://github.com/informalsystems/ibc-rs/issues/1913))
    * Add a new `client` feature to gate the tonic client code, implies the `std` feature.
    * Add a new `json-schema` feature to derive `schemars::JsonSchema` on some proto types, implies the `std` feature.
    * Add `#[serde(default)]` to fields that might be omitted by Golang `omitempty` directive.
    * Change serialization of byte arrays to Base64 for compatibility with Go.
  - Derive `Serialize` and `Deserialize` for `ibc-proto::ibc::core` and `ibc_proto::ibc::applications` structs,
    and switch to Google's Protobuf standard types instead of Prost's types.
    ([#1988](https://github.com/informalsystems/ibc-rs/issues/1988))
- [Relayer Library](relayer)
  - Added caching layer for hermes start command
    ([#1908](https://github.com/informalsystems/ibc-rs/issues/1908))
  - Add support for wildcards in port and channel identifiers in the packet filter configuration,
    which enable operators to filter ICA channels based on the port prefix
    ([#1927](https://github.com/informalsystems/ibc-rs/issues/1927))

### IMPROVEMENTS

- [IBC Modules](modules)
  - Refactored channels events in ICS 04 module
    ([#718](https://github.com/informalsystems/ibc-rs/issues/718))
- [Integration Test Framework](relayer-cli)
  - Split out test framework as new crate `ibc-test-framework` from `ibc-integration-test`. ([#1961](https://github.com/informalsystems/ibc-rs/pull/1961))
- [Relayer Library](relayer)
  - Add documentation for the caching layer implemented in ([#1908](https://github.com/informalsystems/ibc-rs/issues/1908))
- [Relayer CLI](relayer-cli)
  - Print packet data on one line ([#1559](https://github.com/informalsystems/ibc-rs/issues/1559))

## v0.12.0
*February 24th, 2022*

This release notably brings compatibility with Cosmos SDK 0.45 and IBC v3.0.0-rc.0,
as well as support for non-standard ports in the channel handshake.
It also contains a fix for a bug where `SendPacket` events were duplicated when emitted at EndBlock,
and fixes another bug where Hermes would clear packet at startup even when `clear_on_start = false`.
The relayer will now also honor the `tracing` filter specified in the `RUST_LOG` environment variable, if any.

### Note for operators

As of this release, the relayer will not respond to the `SIGHUP` signal and will therefore
not reload the configuration anymore. This feature has been deemed unnecessary given the
recent performance improvements, and it is now recommended to just restart the relayer
when the configuration is updated.

Additionally, a new CLI command [`clear packets`](https://hermes.informal.systems/commands/relaying/clear.html)
has been added for clearing packets in both direction on a given channel.

### BUG FIXES

- [IBC Modules](modules)
  - Fixed the formatting of NotEnoughTimeElapsed and NotEnoughBlocksElapsed
    in Tendermint errors ([#1706](https://github.com/informalsystems/ibc-rs/issues/1706))
  - IBC handlers now retrieve the host timestamp from the latest host consensus
    state ([#1770](https://github.com/informalsystems/ibc-rs/issues/1770))
- [Relayer Library](relayer)
  - Handle non-standard ports in channel handshake
    ([#1837](https://github.com/informalsystems/ibc-rs/issues/1837))
  - Fix duplicate SendPacket events emitted by EndBlock
    ([#1844](https://github.com/informalsystems/ibc-rs/issues/1844))
  - Fix support for non-standard ports in channel handshake
    ([#1861](https://github.com/informalsystems/ibc-rs/issues/1861),
    [#1837](https://github.com/informalsystems/ibc-rs/issues/1837))
  - Fixed bug where Hermes cleared packets at startup, despite
    `clear_on_start = false` ([#1872](https://github.com/informalsystems/ibc-rs/issues/1872))
- [Relayer CLI](relayer-cli)
  - Disable reloading of configuration upon receiving a SIGHUP signal
    ([#1885](https://github.com/informalsystems/ibc-rs/issues/1885))

### FEATURES

- General
  - Upgrade protos and compatibility to IBC v3.0.0-rc.0 and Cosmos SDK v0.45.1
    ([#1797](https://github.com/informalsystems/ibc-rs/issues/1797))
- [Relayer CLI](relayer-cli)
  - Allow overriding the tracing filter with `RUST_LOG` environment variable
    ([#1895](https://github.com/informalsystems/ibc-rs/issues/1895))

### IMPROVEMENTS

- [IBC Modules](modules)
  - Added more unit tests to verify Tendermint ClientState
    ([#1706](https://github.com/informalsystems/ibc-rs/issues/1706))
  - Define CapabilityReader and CapabilityKeeper traits
    ([#1769](https://github.com/informalsystems/ibc-rs/issues/1769))
- [Relayer Library](relayer)
  - Add two more health checks: tx indexing enabled and historical entries > 0
    ([#1388](https://github.com/informalsystems/ibc-rs/issues/1388))
  - Changed `ConnectionEnd::versions` method to be non-allocating by having it return a `&[Version]` instead of `Vec<Version>`
    ([#1880](https://github.com/informalsystems/ibc-rs/pull/1880))
- [Relayer CLI](relayer-cli)
  - Added `clear packets` command, combining the effects of
    `tx raw packet-recv` and `tx raw packet-ack`
    ([#1834](https://github.com/informalsystems/ibc-rs/pull/1834))

## v0.11.1
*February 4th, 2022*

This release mainly adds support for channel events originating from Tendermint ABCI's `BeginBlock` and `EndBlock` methods.

### BUG FIXES

- [Relayer CLI](relayer-cli)
  - Do not require a config file to be present for the `completions` command.
    ([#1822](https://github.com/informalsystems/ibc-rs/pull/1822))

### IMPROVEMENTS

- [Relayer Library](relayer)
  - Increased tx confirmation timeout to 300s to prevent aggressive tx
    resubmission ([#1663](https://github.com/informalsystems/ibc-rs/issues/1663))
  - Handle channel events originating from Tendermint ABCI's BeginBlock and EndBlock methods
    ([#1793](https://github.com/informalsystems/ibc-rs/issues/1793))


## v0.11.0
*January 27th, 2022*

This release notably speeds up the startup time of Hermes,
adds options to the `create client` command to customize the client parameters,
makes the deposit denomination configurable in `tx raw upgrade-chain` via a new `--denom` flag,
and adds a `completions` CLI command to generate shell auto-completion scripts.

### Note for operators

This release includes a breaking change, which requires the configuration file to be edited.
The `mode.packets.filter` configuration option has been removed and is now enabled by default.

Before running Hermes v0.11.0, make sure you remove the `mode.packets.filter` option from the configuration file.

```diff
--- a/config.toml
+++ b/config.toml
@@ -50,18 +50,6 @@ clear_interval = 100
 # Whether or not to clear packets on start. [Default: false]
 clear_on_start = true

-# Enable or disable the filtering mechanism.
-# Valid options are 'true', 'false'.
-# Currently Hermes supports two filters:
-# 1. Packet filtering on a per-chain basis; see the chain-specific
-#   filter specification below in [chains.packet_filter].
-# 2. Filter for all activities based on client state trust threshold; this filter
-#   is parametrized with (numerator = 1, denominator = 3), so that clients with
-#   thresholds different than this will be ignored.
-# If set to 'true', both of the above filters will be enabled.
-# [Default: false]
-filter = false
-
 # Toggle the transaction confirmation mechanism.
 # The tx confirmation mechanism periodically queries the `/tx_search` RPC
 # endpoint to check that previously-submitted transactions
```


### BREAKING CHANGES

- General
  - Update MSRV to Rust 1.58 ([#1765](https://github.com/informalsystems/ibc-rs/issues/1765))
  - Update tendermint-rs dependencies to 0.23.5 ([#1767](https://github.com/informalsystems/ibc-rs/issues/1767))
- [Relayer Library](relayer)
  - Added a `denom` member to `upgrade_chain::UpgradePlanOptions`
    ([#1662](https://github.com/informalsystems/ibc-rs/issues/1662))
- [IBC Modules](modules)
  - Hide `ibc::Timestamp::now()` behind `clock` feature flag ([#1612](https://github.com/informalsystems/ibc-rs/issues/1612))

### BUG FIXES

- [IBC Modules](modules)
  - Verify the client consensus proof against the client's consensus state root and not the host's state root
    [#1745](https://github.com/informalsystems/ibc-rs/issues/1745)
  - Initialize consensus metadata on client creation
    ([#1763](https://github.com/informalsystems/ibc-rs/issues/1763))

### IMPROVEMENTS

- General
  - Improve startup time of the relayer ([#1705](https://github.com/informalsystems/ibc-rs/issues/1705))
      * When scanning a chain with filtering enabled and an allow list, skip scanning all the clients and query the allowed channels directly. This results in much fewer queries and a faster start.
      * Add a `--full-scan` option to `hermes start` to opt out of the fast start mechanism and do a full scan.
  - Update `tendermint-rs` to v0.23.4 and harmonize the dependencies to use a single TLS stack.
    A system installation of OpenSSL is no longer required to build Hermes.
    ([#1641](https://github.com/informalsystems/ibc-rs/issues/1641))
  - Remove 1 second sleep in `generate_tm_block` during testing with mock context.
    ([#1687](https://github.com/informalsystems/ibc-rs/issues/1687))
- [IBC Modules](modules)
  - Extract all `ics24_host::Path` variants into their separate types
    ([#1760](https://github.com/informalsystems/ibc-rs/issues/1760))
  - Disallow empty `CommitmentPrefix` and `CommitmentProofBytes`
    ([#1761](https://github.com/informalsystems/ibc-rs/issues/1761))
- [Relayer Library](relayer)
  - Allow `ChainEndpoint` implementations to fetch any types of clients
    and consensus states ([#1481](https://github.com/informalsystems/ibc-rs/issues/1481))
  - More structural logging in relayer, using tracing spans and key-value pairs.
    ([#1491](https://github.com/informalsystems/ibc-rs/pull/1491))
  - Improved documention w.r.t. keys for Ethermint-based chains
    ([#1785](https://github.com/informalsystems/ibc-rs/issues/1785))
- [Relayer CLI](relayer-cli)
  - Add custom options to the `create client` command.
    ([#836](https://github.com/informalsystems/ibc-rs/issues/836))
  - Make the deposit denomination configurable in `tx raw upgrade-chain` via a new `--denom` flag.
    ([#1662](https://github.com/informalsystems/ibc-rs/issues/1662))
  - Update to abscissa_core 0.6.0-rc.0 and clap 3.x
    ([#1777](https://github.com/informalsystems/ibc-rs/pull/1777))
  - Add `completions` CLI command to generate shell auto-completion scripts.
    ([#1789](https://github.com/informalsystems/ibc-rs/pull/1789))

## v0.10.0
*January 13th, 2021*

This release notably updates the underlying CLI framework (`abscissa`) to version 0.6.0-beta.1,
which now uses `clap` for parsing command line arguments. This substantially improves the UX of the CLI,
by adding support for `--help` flags in subcommands and improving help and usage printouts.

The `--version` option of the `create channel` subcommand has been renamed
to `--channel-version`, with the old name still supported as an alias.
Additionally, the `-h` short flag on many commands is now `-H` to avoid
clashes with the clap-provided short flag for help.

This release also improves the handling of account sequence mismatch errors,
with a recovery mechanism to automatically retry or drop tx upon such errors.

The relayer now also supports dynamic versions in channel open handshake (which is needed by Interchain Accounts), and enables full support for IBC v2.

### BREAKING CHANGES

- General
  - Update MSRV to Rust 1.57
    ([#1660](https://github.com/informalsystems/ibc-rs/issues/1660))
  - Pin tendermint-rs dependencies to =0.23.2
    ([#1665](https://github.com/informalsystems/ibc-rs/pull/1665))
- [IBC Modules](modules)
  - Add the `frozen_height()` method to the `ClientState` trait (includes breaking changes to the Tendermint `ClientState` API).
    ([#1618](https://github.com/informalsystems/ibc-rs/issues/1618))
  - Remove `Timestamp` API that depended on the `chrono` crate:
    ([#1665](https://github.com/informalsystems/ibc-rs/pull/1665)):
    - `Timestamp::from_datetime`; use `From<tendermint::Time>`
    - `Timestamp::as_datetime`, superseded by `Timestamp::into_datetime`
- [Relayer Library](relayer)
  - Improve spawning of supervisor worker tasks ([#1656](https://github.com/informalsystems/ibc-rs/issues/1656))
    - The `Supervisor` struct is removed.
    - Supervisor is now spawned using the `spawn_supervisor` function.
- [Relayer CLI](relayer-cli)
  - Update to abscissa framework version 0.6.0-beta.1, adding support for
    `--help` flags in subcommands and improving help and usage printouts.
    The `--version` option of the `create channel` subcommand has been renamed
    to `--channel-version`, with the old name still supported as an alias.
    Additionally, the `-h` short flag on many commands is now `-H` to avoid
    clashes with the clap-provided short flag for help.
    ([#1576](https://github.com/informalsystems/ibc-rs/pull/1576),
    [#1743](https://github.com/informalsystems/ibc-rs/pull/1743))

### BUG FIXES

- [IBC Modules](modules)
  - Delete packet commitment instead of acknowledgement in acknowledgePacket
    [#1573](https://github.com/informalsystems/ibc-rs/issues/1573)
  - Set the `counterparty_channel_id` correctly to fix ICS04 [`chanOpenAck` handler verification](https://github.com/informalsystems/ibc-rs/blob/master/modules/src/core/ics04_channel/handler/chan_open_ack.rs)
    ([#1649](https://github.com/informalsystems/ibc-rs/issues/1649))
  - Add missing assertion for non-zero trust-level in Tendermint client initialization.
    ([#1697](https://github.com/informalsystems/ibc-rs/issues/1697))
  - Fix conversion to Protocol Buffers of `ClientState`'s `frozen_height` field.
    ([#1710](https://github.com/informalsystems/ibc-rs/issues/1710))
- [Relayer Library](relayer)
  - Handle expired client errors in workers ([#1543](https://github.com/informalsystems/ibc-rs/issues/1543))
  - Perform `execute_schedule` after handling packet commands in packet worker ([#1715](https://github.com/informalsystems/ibc-rs/issues/1715))
  - Do not spawn detect misbehavior task if it is disabled in config [#1750](https://github.com/informalsystems/ibc-rs/issues/1750)

### FEATURES

- General
  - Extend CI test suite to include E2E tests using Gaia v6.0.0 [#1550](https://github.com/informalsystems/ibc-rs/issues/1550)
  - Added the `extra_wallets` parameter to `gm` to create additional funded wallets.
  - Added the possibility of JSON output to `gm` by setting the environment variable `OUTPUT=json`.
  - Added support for fee granters through config file
    ([#1633](https://github.com/informalsystems/ibc-rs/issues/1633))
- [IBC Modules](modules)
  - Implement proof verification for Tendermint client (ICS07).
    ([#1583](https://github.com/informalsystems/ibc-rs/pull/1583))
- [Relayer Library](relayer)
  - Added a recovery mechanism to automatically retry or drop tx upon account
    sequence mismatch errors ([#1264](https://github.com/informalsystems/ibc-rs/issues/1264))
  - Support dynamic versions in channel open handshake & enable full support for
    ibc-go v2 ([#1410](https://github.com/informalsystems/ibc-rs/issues/1410))
  - Allow custom proof-specs in chain config
    ([#1561](https://github.com/informalsystems/ibc-rs/issues/1561))

### IMPROVEMENTS

- General
  - Update `CONTRIBUTING.md` for latest version of unclog
    ([#1634](https://github.com/informalsystems/ibc-rs/issues/1634))
- [IBC Modules](modules)
  - More conventional ad-hoc conversion methods on `Timestamp`
    ([#1665](https://github.com/informalsystems/ibc-rs/pull/1665)):
  - `Timestamp::nanoseconds` replaces `Timestamp::as_nanoseconds`
  - `Timestamp::into_datetime` substitutes `Timestamp::as_datetime`
- [Relayer CLI](relayer-cli)
  - Improve performance of standalone commands by starting the event monitor on-demand
    ([#1063](https://github.com/informalsystems/ibc-rs/issues/1063))
  - Increase the default for `max_gas` from `300_000` to `400_000`
    ([#1636](https://github.com/informalsystems/ibc-rs/pull/1636))

## v0.9.0, the “Zamfir” release
*November 23rd, 2021*

> This release honors Anca Zamfir, who has lead ibc-rs from its inception and through its first two years of life.
> The whole team is grateful for her dedication and the nurturing environment she created.
> To many more achievements, Anca!! 🥂

#### Notice for operators

This release requires operators to update their Hermes configuration.
The `mode` configuration section now replaces the `strategy` option.

##### `strategy = 'packets'`

If Hermes was configured with `strategy = 'packets'`, then the configuration needs to be changed in the following way:

```diff
 [global]
-strategy = 'packets'
 log_level = 'trace'
-clear_packets_interval = 100
-tx_confirmation = true
+
+[mode]
+
+[mode.clients]
+enabled = true
+refresh = true
+misbehaviour = true
+
+[mode.connections]
+enabled = false
+
+[mode.channels]
+enabled = false
+
+[mode.packets]
+enabled = true
+clear_interval = 100
+clear_on_start = true
+filter = false
+tx_confirmation = true
```

##### `strategy = 'all'`

If Hermes was configured to complete connection and channel handshakes as well, ie. with `strategy = 'all'`,
then on top of the changes above, `mode.connections.enabled` and `mode.channels.enabled` must be set to `true`.

[See the relevant section][config-mode-toml] of the documented `config.toml` file in the repository for more details.

[config-mode-toml]: https://github.com/informalsystems/ibc-rs/blob/v0.9.0/config.toml#L9-L59


### BUG FIXES

- [IBC Modules](modules)
  - Set the connection counterparty in the ICS 003 [`connOpenAck` handler][conn-open-ack-handler]
    ([#1532](https://github.com/informalsystems/ibc-rs/issues/1532))

[conn-open-ack-handler]: https://github.com/informalsystems/ibc-rs/blob/master/modules/src/core/ics03_connection/handler/conn_open_ack.rs

### FEATURES

- General
  - Support for compatibility with gaia Vega upgrade (protos matching ibc-go v1.2.2 and SDK v0.44.3)
    ([#1408](https://github.com/informalsystems/ibc-rs/issues/1408))
  - Optimize the WS client to subscribe to IBC events only (instead of all Tx
    events) ([#1534](https://github.com/informalsystems/ibc-rs/issues/1534))
- [Relayer Library](relayer)
  - Allow for more granular control of relaying modes. The `mode` configuration section replaces the `strategy` option.
    ([#1518](https://github.com/informalsystems/ibc-rs/issues/1518))

### IMPROVEMENTS

- General
  - Upgrade IBC-rs TLA+ MBT models to modern Apalache type annotations
    ([#1544](https://github.com/informalsystems/ibc-rs/issues/1544))
  - Add `architecture.md` doc that gives a high-level overview of the structure of the codebase
  - Add some module-level documentation ([#1556](https://github.com/informalsystems/ibc-rs/pulls/1556))
- [IBC Modules](modules)
  - Derive `PartialEq` and `Eq` on `IbcEvent` and inner types
    ([#1546](https://github.com/informalsystems/ibc-rs/issues/1546))
- [Relayer Library](relayer)
  - The relayer will now avoid submitting a tx after the simulation failed
    (in all but one special case) to avoid wasting fees unnecessarily
    ([#1479](https://github.com/informalsystems/ibc-rs/issues/1479))
- [Relayer CLI](relayer-cli)
  - Output errors on a single line if ANSI output is disabled
    ([#1529](https://github.com/informalsystems/ibc-rs/issues/1529))
  - Compute fee amount using big integers to prevent overflow
    when using denominations with high decimal places
    ([#1555](https://github.com/informalsystems/ibc-rs/issues/1555))

## v0.8.0
*October 29th, 2021*

This is the final release of version 0.8.0, which now depends on the official releases of the `prost` and `tonic` crates.
In addition to everything that's included in v0.8.0-pre.1, this release updates the minimum supported Rust version to 1.56, 
and contains various bug fixes and performance improvements which make the relayer more reliable.

#### Notice for operators
A new setting was added to the Hermes configuration: `max_block_time`.
This setting specifies the maximum time per block for this chain.
The block time together with the clock drift are added to the source drift to estimate
the maximum clock drift when creating a client on this chain.
For Cosmos-SDK chains a good approximation is `timeout_propose` + `timeout_commit`

### BREAKING CHANGES

- Update MSRV to Rust 1.56 and use the 2021 edition
  ([#1519](https://github.com/informalsystems/ibc-rs/issues/1519))

### BUG FIXES

- Fix for "new header has a time from the future" chain error which would arise due to clock drift ([#1445](https://github.com/informalsystems/ibc-rs/issues/1445)):
  * Added new config param `max_block_time` to prevent the problem for appearing in newly-created clients.
  * Added a synchronous waiting in client update logic to allow destination chain to reach a new height
    before submitting a client update message.
- Ensure Hermes does not send timeouts for packets that have not expired yet
    ([#1504](https://github.com/informalsystems/ibc-rs/issues/1504))

### IMPROVEMENTS

- General
  - Update to official releases of `prost` 0.9 and `tonic` 0.6
    ([#1502](https://github.com/informalsystems/ibc-rs/issues/1502))
- [IBC Modules](modules)
  - Support for converting `ibc::events::IbcEvent` into `tendermint::abci::Event` 
    ([#838](https://github.com/informalsystems/ibc-rs/issues/838))
  - Restructure the layout of the `ibc` crate to match `ibc-go`'s [layout](https://github.com/cosmos/ibc-go#contents)
    ([#1436](https://github.com/informalsystems/ibc-rs/issues/1436))
  - Implement `FromStr<Path>` to enable string-encoded paths to be converted into Path identifiers
    ([#1460](https://github.com/informalsystems/ibc-rs/issues/1460))
- [Relayer Library](relayer)
  - Improve performance of misbehaviour checks triggered by an `UpdateClient` event
    ([#1417](https://github.com/informalsystems/ibc-rs/issues/1417))

## v0.8.0-pre.1
*October 22nd, 2021*

This is a pre-release which depends on in-house forks of various Rust libraries.
As such, it is advised to avoid depending on the `ibc` and `ibc-relayer` crates
at version 0.8.0-pre.1.

Hermes v0.8.0-pre.1 is considered stable and it is recommended for all
users to update to this version.

This release notably includes a new [`memo_prefix`][memo] configuration option
for specifying a prefix to be included in the memo of each transaction submitted
by Hermes.

Moreover, Hermes is now able to handle `SendPacket` events originating from Tendermint
ABCI's `BeginBlock` and `EndBlock` methods ([#1231](https://github.com/informalsystems/ibc-rs/issues/1231)).

[memo]: https://github.com/informalsystems/ibc-rs/blob/v0.8.0-pre.1/config.toml#L161-L165

### BREAKING CHANGES

- [IBC Modules](modules)
  - The `check_header_and_update_state` method of the `ClientDef`
    trait (ICS02) has been expanded to facilitate ICS07
    ([#1214](https://github.com/informalsystems/ibc-rs/issues/1214))

### FEATURES

- General
  - Add support for the `tx.memo` field
    ([#1433](https://github.com/informalsystems/ibc-rs/issues/1433))
- [IBC Modules](modules)
  - Add ICS07 verification functionality by using `tendermint-light-client`
    ([#1214](https://github.com/informalsystems/ibc-rs/issues/1214))
- [Relayer Library](relayer)
  - Add a `default_gas` setting to be used for submitting a tx when tx simulation
    fails ([#1457](https://github.com/informalsystems/ibc-rs/issues/1457))
  - Update compatibility check for IBC-Go dependency
    ([#1464](https://github.com/informalsystems/ibc-rs/issues/1464))

### IMPROVEMENTS

- [Relayer Library](relayer)
  - Handle SendPacket events originating from Tendermint ABCI's BeginBlock
    and EndBlock methods ([#1231](https://github.com/informalsystems/ibc-rs/issues/1231))
  - Improve error message when `create client` fails and add a health
    check for the trusting period being smaller than the unbonding period
    ([#1440](https://github.com/informalsystems/ibc-rs/issues/1440))

## v0.7.3
*October 4th, 2021*

This minor release most notably includes a fix for a bug introduced in v0.7.0
where Hermes would always use the max gas when submitting transactions to
chains based on Cosmos SDK <= 0.42.
It also improves the handling of account sequence numbers

### BUG FIXES

- [Relayer Library](relayer)
  - Fix a bug introduced in Hermes v0.7.0 where tx simulations would fail on
    chains based on Cosmos SDK 0.42. This would cause Hermes to use the max
    gas specified in the config when submitted the tx, leading to high fees.
    ([#1345](https://github.com/informalsystems/ibc-rs/issues/1345))
  - Only increase cached account sequence number when `broadcast_tx_sync` fails,
    therefore ensuring that the cached sequence number stays in sync with the
    node. ([#1402](https://github.com/informalsystems/ibc-rs/issues/1402))

### IMPROVEMENTS

- [Relayer Library](relayer)
  - Set default trusting period to be 2/3 of unbonding period for Cosmos chains
    ([#1392](https://github.com/informalsystems/ibc-rs/issues/1392))

## v0.7.2
*September 24th, 2021*

This minor release brings substantial performance improvements as well as
support for chains using Secp256k1 signatures in consensus votes.

It also bumps the compatibility to Cosmos SDK 0.44.

### FEATURES

- Support for chains which use Secp256k1 signatures in consensus votes ([#1155](https://github.com/informalsystems/ibc-rs/issues/1155))
- Modified packet worker to use stubborn strategy ([#1290](https://github.com/informalsystems/ibc-rs/issues/1290))
- Skip `consensus_heights` query in `update_client` when possible ([#1362](https://github.com/informalsystems/ibc-rs/issues/1362))
- Support for disabling tx confirmation mechanism ([#1380](https://github.com/informalsystems/ibc-rs/issues/1380))

- [gm](scripts/gm)
  - Binaries in the config can be defined as URLs now.
  - Add the option to set gm-lib path via the `$GM_LIB` environment variable ([#1365](https://github.com/informalsystems/ibc-rs/issues/1365))

### IMPROVEMENTS

- Use `core` and `alloc` crates for `no_std` compatibility ([#1156](https://github.com/informalsystems/ibc-rs/issues/1156))
- Improve performance of health check, and only perform it on `hermes start`.
  Add a `hermes health-check` command. ([#1336](https://github.com/informalsystems/ibc-rs/issues/1336))
- Treat pre-releases of the Cosmos SDK as their standard version in compatibility check ([#1337](https://github.com/informalsystems/ibc-rs/issues/1337))
- Bump Cosmos SDK compatibility to v0.44.0 ([#1344](https://github.com/informalsystems/ibc-rs/issues/1344))
- Improve reliability of health check ([#1382](https://github.com/informalsystems/ibc-rs/issues/1376))

## v0.7.1
*September 14th, 2021*

This minor release of Hermes notably features support for Ethermint chains and transfer amounts expressed as a 256-bit unsigned integer.
This release also fixes a bug where the chain runtime within the relayer would crash when failing to decode a invalid header included in a `ClientUpdate` IBC event.

### BUG FIXES

- Fix header decoding error which resulted in killing the chain runtime ([#1342](https://github.com/informalsystems/ibc-rs/issues/1342))

- [gm](scripts/gm)
  - Fix gaiad keys add prints to stderr instead of stdout in SDK 0.43 ([#1312])
  - Bumped default `rpc_timeout` in Hermes config to 5 seconds ([#1312])

[#1312]: https://github.com/informalsystems/ibc-rs/issues/1312

### FEATURES

- Added post-Stargate (v0.5+) Ethermint support ([#1267] [#1071])

[#1267]: https://github.com/informalsystems/ibc-rs/issues/1267
[#1071]: https://github.com/informalsystems/ibc-rs/issues/1071

### IMPROVEMENTS

- General
  - Derive `Debug`, `PartialEq` and `Eq` traits for module errors ([#1281])
  - Add MBT tests for ICS 07 Client Upgrade ([#1311])
  - Add support for uint256 transfer amounts ([#1319])

- [ibc](modules)
  - Change all `*Reader` traits to return `Result` instead of `Option` ([#1268])
  - Clean up modules' errors ([#1333])

[#1268]: https://github.com/informalsystems/ibc-rs/issues/1268
[#1281]: https://github.com/informalsystems/ibc-rs/issues/1281
[#1311]: https://github.com/informalsystems/ibc-rs/issues/1311
[#1319]: https://github.com/informalsystems/ibc-rs/issues/1319
[#1333]: https://github.com/informalsystems/ibc-rs/issues/1333

## v0.7.0
*August 24th, 2021*

This release of Hermes is the first to be compatible with the development version of Cosmos SDK 0.43.
Hermes 0.7.0 also improves the performance and reliability of the relayer, notably by waiting asynchronously for transactions to be confirmed.
Additionnally, Hermes now includes a REST server which exposes the relayer's internal state over HTTP.

### BUG FIXES

- [ibc](modules)
  - Set the index of `ibc::ics05_port::capabilities::Capability` ([#1257])

- [gm](scripts/gm)
  - Fix silent exit when requirements are missing

[#1257]: https://github.com/informalsystems/ibc-rs/issues/1257
[#1261]: https://github.com/informalsystems/ibc-rs/issues/1261

### FEATURES

- General
  - Update CI to test with gaiad v5.0.5 ([#1175])

- [ibc-relayer-cli](relayer-cli)
  - Add `keys delete` CLI command ([#1065])
  - Add `--legacy | -l` flag to support upgrades for chains built with Cosmos SDK < v0.43.0 ([#1287])

- [ibc-relayer](relayer)
  - Expose the Hermes config and internal state over a REST API ([#843])
  - Spawn packet workers only when there are outstanding packets or acknowledgements to relay ([#901])
  - Upgrade to Cosmos SDK proto (v0.43.0) & ibc-go proto (v1.0.0) ([#948])

[#843]: https://github.com/informalsystems/ibc-rs/issues/843
[#901]: https://github.com/informalsystems/ibc-rs/issues/901
[#948]: https://github.com/informalsystems/ibc-rs/pull/948
[#1065]: https://github.com/informalsystems/ibc-rs/issues/1065
[#1175]: https://github.com/informalsystems/ibc-rs/issues/1175
[#1287]: https://github.com/informalsystems/ibc-rs/issues/1287

### IMPROVEMENTS

- General
  - Update Modelator to 0.2.0 ([#1249])

- [ibc-relayer-cli](relayer-cli)
  - Add optional destination chain and `--verbose` options for `query channels` CLI ([#1132])

- [ibc-relayer](relayer)
  - Improve support for Interchain Accounts (ICS 027) ([#1191])
  - Improve performance and reliability of the relayer by asynchronously waiting for tx confirmations ([#1124], [#1265])

- [ibc](modules)
  - Implement `ics02_client::client_consensus::ConsensusState` for `AnyConsensusState` ([#1297])

[#1124]: https://github.com/informalsystems/ibc-rs/issues/1124
[#1132]: https://github.com/informalsystems/ibc-rs/issues/1132
[#1191]: https://github.com/informalsystems/ibc-rs/issues/1191
[#1249]: https://github.com/informalsystems/ibc-rs/pull/1249
[#1265]: https://github.com/informalsystems/ibc-rs/issues/1265
[#1297]: https://github.com/informalsystems/ibc-rs/issues/1297

## v0.6.2
*August 2nd, 2021*

This minor release of Hermes re-enables the `upgrade client`, `upgrade clients`,
`tx raw upgrade-clients`, and `tx raw upgrade-chain`, and otherwise
contains a few bug fixes and internal improvements.

Upgrading from version `0.6.1` to `0.6.2` requires no explicit steps.

### BUG FIXES

- Add missing `Protobuf` impl for `ics03_connection::connection::Counterparty` ([#1247])

[#1247]: https://github.com/informalsystems/ibc-rs/issues/1247

### FEATURES

- Use the [`flex-error`](https://docs.rs/flex-error/) crate to define and
handle errors ([#1158])

[#1158]: https://github.com/informalsystems/ibc-rs/issues/1158
- Augment ClientCreationFailed error with chain id and WS address ([#1020])

[#1020]: https://github.com/informalsystems/ibc-rs/issues/1020
- Improve the error message for config file parse errors ([#1021])

[#1021]: https://github.com/informalsystems/ibc-rs/issues/1021
- Fix for upgrade CLI regression using new type ics02::TrustThreshold ([#1229])

[#1229]: https://github.com/informalsystems/ibc-rs/issues/1229

### IMPROVEMENTS

- Add semantic validation of of `max_tx_size` and `max_num_msg` config options ([#1245])

[#1245]: https://github.com/informalsystems/ibc-rs/issues/1245

## v0.6.1
*July 22nd, 2021*

This minor release mainly improves the reliability of the relayer
by ensuring that pending packets are cleared on start,
and that Hermes can recover from the WebSocket subscriptions
being closed under its feet by Tendermint.

Upgrading from version `0.6.0` to `0.6.1` requires no explicit steps.

> **WARNING:** Due to a regression ([#1229]), the `upgrade client`,
> `tx raw upgrade-clients`, and `tx raw upgrade-chain` commands have
> been temporarily disabled in this version.
> These commands will be re-enabled in the next version.

### FEATURES

- [ibc]
  - Enable `pub` access to verification methods of ICS 03 & 04 ([#1198])
  - Add `ics26_routing::handler::decode` function ([#1194])
  - Add a pseudo root to `MockConsensusState` ([#1215])

### IMPROVEMENTS

- [ibc-relayer-cli]
  - Add CLI git hash ([#1094])
  - Fix unwraps in `packet query` CLIs ([#1114])

### BUG FIXES

- [ibc]
  - Fix stack overflow in `MockHeader` implementation ([#1192])
  - Align `as_str` and `from_str` behavior in `ClientType` ([#1192])

- [ibc-relayer]
  - Ensure pending packets are cleared on start ([#1200])
  - Recover from missed RPC events after WebSocket subscription is closed by Tendermint ([#1196])


[#1094]: https://github.com/informalsystems/ibc-rs/issues/1094
[#1114]: https://github.com/informalsystems/ibc-rs/issues/1114
[#1192]: https://github.com/informalsystems/ibc-rs/issues/1192
[#1194]: https://github.com/informalsystems/ibc-rs/issues/1194
[#1196]: https://github.com/informalsystems/ibc-rs/issues/1196
[#1198]: https://github.com/informalsystems/ibc-rs/issues/1198
[#1200]: https://github.com/informalsystems/ibc-rs/issues/1200
[#1215]: https://github.com/informalsystems/ibc-rs/issues/1215
[#1229]: https://github.com/informalsystems/ibc-rs/issues/1229


## v0.6.0
*July 12th, 2021*


Many thanks to Fraccaroli Gianmarco (@Fraccaman) for helping us improve the
reliability of Hermes ([#697]).

This release includes two major features to Hermes: (1) support for reloading
the chains from the configuration file at runtime, and (2) a filtering mechanism
to restrict Hermes activity based on predefined parameters (e.g., packet relaying
on certain ports and channels exclusively, and ignoring activity for clients
that have non-standard trust threshold).

In addition to these two, we have also added a health checkup mechanism, plus new
`config validate` and `query channel ends` CLIs.

### Upgrading from 0.5.0 to 0.6.0

When upgrading from Hermes v0.5.0 to v0.6.0, the most important
point to watch out for is the configuration file.
The Hermes config.toml configuration file has went through a few revisions,
with the changes described below.

#### Added inline documentation for all options.

Please have a look around the [config.toml](https://github.com/informalsystems/ibc-rs/blob/v0.6.0/config.toml) directly.

#### Added a packet filtering mechanism based on channel/port identifiers

This feature will restrict the channels on which Hermes relays packets.
There are two new options in the configuration file:

1. A global `filter` parameter to enable or disable filtering globally.
2. A per-chain `.filters` option that expects a `policy` (either `allow` or
   `deny`) plus a list of channel and
   port identifiers. If policy is `allow`, then packet relaying will be restricted to this
   list for the corresponding chain. If the policy is `deny`, then any packets
   from this list will be ignored.

#### Added filtering based on client state

The global `filter` option additionally enables filtering of all activities
based on client state trust threshold. If enabled, Hermes will ignore all
activity for clients that have a trust threshold different than `1/3`.

#### Added a packet clearing configuration option

This will enable the parametrization of the frequency
at which Hermes will clear pending packets. This is a global option, called
`clear_packets_interval`, which applies to all chains in the configuration.


The full list of changes is described below.

### FEATURES

- [ibc-relayer]
  - The chains configuration can be reloaded by sending the Hermes process a `SIGHUP` signal ([#1117])
  - Added support for filtering based on client state trust threshold ([#1165])

- [ibc-relayer-cli]
  - Added `config validate` CLI to Hermes ([#600])
  - Added filtering capability to deny or allow for specific channels ([#1140], [#1141], [#69])
  - Added basic channel filter ([#1140])
  - Added `query channel ends` CLI command ([#1062])
  - Added a health checkup mechanism for Hermes ([#697, #1057])

### IMPROVEMENTS

- Update to `tendermint-rs` v0.20.0 ([#1125])
- Add inline documentation to config.toml ([#1127])

- [ibc-relayer]
  - Hermes will now clear pending packets at a configurable interval ([#1124])

### BUG FIXES

- [ibc-relayer]
  - Fix for schedule refreshing bug ([#1143])


[#69]: https://github.com/informalsystems/ibc-rs/issues/69
[#600]: https://github.com/informalsystems/ibc-rs/issues/600
[#697]: https://github.com/informalsystems/ibc-rs/issues/697
[#1062]: https://github.com/informalsystems/ibc-rs/issues/1062
[#1117]: https://github.com/informalsystems/ibc-rs/issues/1117
[#1057]: https://github.com/informalsystems/ibc-rs/issues/1057
[#1125]: https://github.com/informalsystems/ibc-rs/issues/1125
[#1124]: https://github.com/informalsystems/ibc-rs/issues/1124
[#1127]: https://github.com/informalsystems/ibc-rs/issues/1127
[#1140]: https://github.com/informalsystems/ibc-rs/issues/1140
[#1141]: https://github.com/informalsystems/ibc-rs/issues/1141
[#1143]: https://github.com/informalsystems/ibc-rs/issues/1143
[#1165]: https://github.com/informalsystems/ibc-rs/issues/1165


## v0.5.0
*June 22nd, 2021*

This release brings a few features, and several improvements and bug fixes to the Hermes
relayer, notably the capability for Hermes to complete IBC connection handshakes when
it detects that one has been initialized, as well as the ability to detect chain
impersonation attacks and to dynamically estimate the gas needed to submit
a transaction.

Moreover, the overall reliability and availability of the relayer has also been improved
substantially by switching over to `tx_broadcast_sync` for submitting transactions.

### FEATURES

- [ibc-relayer-cli]
  - Add `--hd-path` option to `keys restore` and `keys add` commands to specify
    derivation path when importing keys ([#1049])

- [ibc-relayer]
  - Event-based handshake completion for IBC connections ([#821])
  - Enable TLS support for gRPC client ([#877])

### IMPROVEMENTS

- [ibc-relayer-cli]
  - Minor log output improvements: color enabled, reduced redundant information ([#1100])

- [ibc-relayer]
  - Update the on-chain IBC client with supporting headers when light client verification
    performs bisection when verifying a header for a client update or a misbehaviour detection ([#673])
  - Add mitigation for chain impersonation attacks ([#1038])
  - Determine gas fee dynamically per transaction ([#930])
  - Submit transactions with `broadcast_tx_sync` and keep track of account sequences ([#986])

### BUG FIXES

- [gaiad-manager]
  - Removed the testnet command as not all networks support it ([#1050])
  - Update for compatibility with Hermes's new `--hd-path` option

- [ibc-relayer]
  - Fix bug where channels were left partially open after `channel create` ([#1064])
  - Prevent account sequence mismatch errors in many cases ([#919], [#978])
  - Prevent timeouts when submitting transactins ([#977])

### BREAKING CHANGES

- [ibc-relayer-cli]
  - Removed `--coin-type` option from `keys restore` command. Use `--hd-path` instead ([#1049])

[#673]: https://github.com/informalsystems/ibc-rs/issues/673
[#821]: https://github.com/informalsystems/ibc-rs/issues/821
[#877]: https://github.com/informalsystems/ibc-rs/issues/877
[#919]: https://github.com/informalsystems/ibc-rs/issues/919
[#930]: https://github.com/informalsystems/ibc-rs/issues/930
[#977]: https://github.com/informalsystems/ibc-rs/issues/977
[#978]: https://github.com/informalsystems/ibc-rs/issues/978
[#986]: https://github.com/informalsystems/ibc-rs/issues/986
[#1038]: https://github.com/informalsystems/ibc-rs/issues/1038
[#1049]: https://github.com/informalsystems/ibc-rs/issues/1049
[#1050]: https://github.com/informalsystems/ibc-rs/issues/1050
[#1064]: https://github.com/informalsystems/ibc-rs/issues/1064
[#1100]: https://github.com/informalsystems/ibc-rs/issues/1100

## v0.4.0
*June 3rd, 2021*

- This release of Hermes features an internal [telemetry service][telemetry]
  which can export metrics about the relayer to Prometheus.
- A new [relaying strategy][strategy] is now available, which enables Hermes to
  complete channel handshakes in an event-based fashion.
- Hermes now checks if another relayer may have already processed a packet event,
  and will not attempt to process it itself, which improves performance.
- The startup time of the relayer has been substantially improved.
- The `start-multi` command has been promoted to `start`, which means
  that the worker-based relayer is not experimental anymore.
- A regression where Hermes would not recover after a node went down and up again was fixed.

[telemetry]: https://hermes.informal.systems/telemetry.html
[strategy]: http://hermes.informal.systems/config.html?highlight=strategy#global

> Special thanks to Colin Axnér (@colin-axner) and Jongwhan Lee (@leejw51crypto)
> for raising multiple issues that helped us improve the reliability of Hermes.

### FEATURES

- [ibc-relayer]
  - Add telemetry and Prometheus endpoint ([#868], [#1032])
  - Add support for event based channel relaying ([#822])
  - Graceful handling of packet events in the presence of multiple relayers ([#983])

### IMPROVEMENTS

- [ibc]
  - Started `unwrap` cleanup ([#871])

- [ibc-relayer-cli]
  - Include chain-id in `query clients` command, and sort output by client counter ([#992])
  - Improve config loading message ([#996])
  - Improve Hermes worker spawn time for `start` command ([#998])
  - Better Hermes help message when command is unrecognized ([#1003])

### BUG FIXES

- [ibc-relayer]
  - Fix client worker initialization error ([#972])
  - Fix `hermes start` panic when all chains are unreachable ([#972])
  - Ensure expired or frozen client worker logs message and terminates ([#1022])
  - Fix regression where Hermes would not recover after a node went down and up again ([#1026])

- [gaiad-manager]
  - Import hermes keys properly even if wallet HD derivation path is set ([#975])
  - Apply default values to missing configuration parameters ([#993])
  - `gm hermes config` now creates hermes 0.4.0 compatible configuration ([#1039])

### BREAKING CHANGES

- [ibc-relayer-cli]
  - Promote `start-multi` command to `start` ([#911])

[#822]: https://github.com/informalsystems/ibc-rs/issues/822
[#868]: https://github.com/informalsystems/ibc-rs/issues/868
[#871]: https://github.com/informalsystems/ibc-rs/issues/871
[#911]: https://github.com/informalsystems/ibc-rs/issues/911
[#972]: https://github.com/informalsystems/ibc-rs/issues/972
[#975]: https://github.com/informalsystems/ibc-rs/issues/975
[#983]: https://github.com/informalsystems/ibc-rs/issues/983
[#992]: https://github.com/informalsystems/ibc-rs/issues/992
[#996]: https://github.com/informalsystems/ibc-rs/issues/996
[#993]: https://github.com/informalsystems/ibc-rs/issues/993
[#998]: https://github.com/informalsystems/ibc-rs/issues/998
[#1003]: https://github.com/informalsystems/ibc-rs/issues/1003
[#1022]: https://github.com/informalsystems/ibc-rs/issues/1022
[#1026]: https://github.com/informalsystems/ibc-rs/issues/1026
[#1032]: https://github.com/informalsystems/ibc-rs/issues/1032
[gaiad-manager]: https://github.com/informalsystems/ibc-rs/blob/master/scripts/gm/README.md
[#1039]: https://github.com/informalsystems/ibc-rs/issues/1039

## v0.3.2
*May 21st, 2021*

This is minor release which brings substantial performance improvements
to the relayer (relaying 1000 packets now takes 2-5min instead of 1h+),
better UX for the `ft-transfer` command, and automatic deployment of
Docker images to Docker Hub.

### FEATURES

- [ibc-relayer-cli]
  - Add a `--key` option to the tx raw ft-transfer command to override the account used for sending messages ([#963])

- [ibc-relayer]
  - Add support for multiple keys to the keyring ([#963])

- [release]
  - Released the official [Hermes image][hermes-docker] on Docker Hub ([#894])
  - Automatically deploy Docker Hub image during release ([#967])

### IMPROVEMENTS

- [ibc-relayer]
  - Batch together all events from all transactions included in a block ([#957])

### BUG FIXES

- [ibc-relayer-cli]
  - Prevent sending `ft-transfer` MsgTransfer on a non-Open channel ([#960])

### BREAKING CHANGES

> Nothing

[#868]: https://github.com/informalsystems/ibc-rs/issues/868
[#894]: https://github.com/informalsystems/ibc-rs/pull/894
[#957]: https://github.com/informalsystems/ibc-rs/issues/957
[#960]: https://github.com/informalsystems/ibc-rs/issues/960
[#963]: https://github.com/informalsystems/ibc-rs/issues/963
[#967]: https://github.com/informalsystems/ibc-rs/issues/967

[hermes-docker]: https://hub.docker.com/r/informalsystems/hermes

## v0.3.1
*May 14h, 2021*

This release improves the UX of a couple commands, fixes a bug related
to delay periods, and adds support for packet timeouts based on timestamps,
as well as support Protobuf-encoded keys.

### FEATURES

- [scripts]
  - Created the Gaiad Manager `gm` CLI tool for managing gaiad instances on the local machine ([#902])

- [ibc-relayer]
  - Add support for packet timeout based on timeout timestamp ([#937])
  - Added support for Protobuf-based Keyring ([#925])

### IMPROVEMENTS

- [ibc-relayer-cli]
  - Improve UX when querying non-existing connections and channels ([#875], [#920])
  - More details in error messages to increase debuggability ([#921], [#934])
  - Disallow creating a client with same source and destination chains ([#932])
  - Make packet worker more resilient to nodes being unreachable for a short amount of time ([#943])

### BUG FIXES

- [ibc]
  - Process raw `delay_period` field as nanoseconds instead of seconds. ([#927])

### BREAKING CHANGES

> Nothing


[#875]: https://github.com/informalsystems/ibc-rs/issues/875
[#920]: https://github.com/informalsystems/ibc-rs/issues/920
[#902]: https://github.com/informalsystems/ibc-rs/issues/902
[#921]: https://github.com/informalsystems/ibc-rs/issues/921
[#925]: https://github.com/informalsystems/ibc-rs/issues/925
[#927]: https://github.com/informalsystems/ibc-rs/issues/927
[#932]: https://github.com/informalsystems/ibc-rs/issues/932
[#934]: https://github.com/informalsystems/ibc-rs/issues/934
[#937]: https://github.com/informalsystems/ibc-rs/issues/937
[#943]: https://github.com/informalsystems/ibc-rs/issues/943


## v0.3.0
*May 7h, 2021*

Special thanks to Jongwhan Lee (@leejw51crypto) for his contributions ([#878]).

This release mostly focuses on improving the UX and the experimental multi-paths relayer (`start-multi` command),
which has been made more resilient against nodes going down, and is now able to clear pending packets
and periodically refresh IBC clients. The relayer now also supports [ICS 027 (Interchain Accounts)][ics27].

[ics27]: https://github.com/cosmos/ibc/blob/master/spec/app/ics-027-interchain-accounts/README.md

### FEATURES

- [ibc-relayer]
  - Support for ICS27 ([#794])

- [ibc-relayer-cli]
  - Added packet clearing and client refresh capabilities for the `start-multi` command ([#784], [#786])

### IMPROVEMENTS

- [ibc]
  - Reinstated `ics23` dependency ([#854])
  - Use proper Timestamp type to track time ([#758])

- [ibc-relayer]
  - Change the default for client creation to allow governance recovery in case of expiration or misbehaviour ([#785])
  - Use a single supervisor in `start-multi` to subscribe to all configured chains ([#862])
  - The `start-multi` command is now more resilient to a node not being up or going down, and will attempt to reconnect ([#871])

### BUG FIXES

- [ibc]
  - Fix parsing in `chain_version` when chain identifier has multiple dashes ([#878])

- [ibc-relayer]
  - Fix pagination in gRPC query for clients ([#811])
  - Fix relayer crash when hermes starts in the same time as packets are being sent ([#851])
  - Fix missing port information in `hermes query channels` ([#840])
  - Fix crash during initialization of event monitor when node is down ([#863])
  - Spawn a single Tokio runtime for the whole supervisor instead of one per chain ([#909])

- [ibc-relayer-cli]
  - Fix for `ft-transfer` mismatching arguments ([#869])
  - Fix channel destination chain mismatch on unreceived-packets or unreceived-acks ([#873])

### BREAKING CHANGES

- [ibc-relayer]
  - `hermes -j query channels` command now returns `result` array with the format
    `[{"channel_id":"channel-0","port_id":"transfer"}, ...]` instead of `["channel-0", ...]` ([#840])


[#758]: https://github.com/informalsystems/ibc-rs/issues/758
[#784]: https://github.com/informalsystems/ibc-rs/issues/784
[#785]: https://github.com/informalsystems/ibc-rs/issues/785
[#786]: https://github.com/informalsystems/ibc-rs/issues/786
[#794]: https://github.com/informalsystems/ibc-rs/issues/794
[#811]: https://github.com/informalsystems/ibc-rs/issues/811
[#840]: https://github.com/informalsystems/ibc-rs/issues/840
[#851]: https://github.com/informalsystems/ibc-rs/issues/851
[#854]: https://github.com/informalsystems/ibc-rs/issues/854
[#862]: https://github.com/informalsystems/ibc-rs/issues/862
[#863]: https://github.com/informalsystems/ibc-rs/issues/863
[#869]: https://github.com/informalsystems/ibc-rs/issues/869
[#871]: https://github.com/informalsystems/ibc-rs/issues/871
[#873]: https://github.com/informalsystems/ibc-rs/issues/873
[#878]: https://github.com/informalsystems/ibc-rs/issues/878
[#909]: https://github.com/informalsystems/ibc-rs/issues/909

## v0.2.0
*April 14th, 2021*

This release includes initial support for relaying over multiple paths from a single `hermes` instance.
Adds support for relayer restart, where pending packets are cleared.
Includes support for ordered channels, packet delay, misbehaviour detection and evidence submission, client upgrade after counterparty chain upgrades.

This release brings improvements to the relayer UX by providing new and updated commands for keys, client, connection and channel management.
In addition, it simplifies the configuration of and integration with the light client.

This release also finalizes the initial implementation of all the ICS 004 handlers.

### FEATURES

- Update to `tendermint-rs` v0.19.0 ([#798])

- [ibc]
  - Added handler(s) for sending packets ([#695]), recv. and ack. packets ([#736]), and timeouts ([#362])

- [ibc-relayer]
  - Support for relayer restart ([#561])
  - Add support for ordered channels ([#599])
  - Misbehaviour detection and evidence submission ([#632])
  - Use a stateless light client without a runtime ([#673])

- [ibc-relayer-cli]
  - Added `create connection` and `create channel` CLIs ([#630], [#715])
  - Proposed ADR 006 to describe Hermes v0.2.0 use-cases ([#637])
  - Added `client-upgrade` CLI ([#357])
  - Added delay feature for packet relaying ([#640])
  - Update gaia to version 4.2.0 for e2e tests on CI ([#809])
  - Add `start-multi` command to relay on all paths defined in the configuration ([#748])
  - Add option to specify which events to listen for in `listen` command ([#550])
  - Add option to customise receiver address for `ft-transfer` command ([#806])
  - Add `keys restore` command to import a signing key from its mnemonic ([#813])

### IMPROVEMENTS

- [ibc]
  - Follow Rust guidelines naming conventions ([#689])
  - Per client structure modules ([#740])
  - MBT: use modelator crate ([#761])

- [ibc-relayer]
  - Consistent identifier handling across ICS 02, 03 and 04 ([#622])

- [ibc-relayer-cli]
  - Clarified success path for updating a client that is already up-to-date ([#734])
  - Added `create` and `update` wrappers for client raw commands ([#772])
  - Output by default is human-readable, and JSON is optional ([#805])

### BUG FIXES

- [ibc]
  - Fix overflow bug in ICS03 client consensus height verification method ([#685])
  - Allow a conn open ack to succeed in the happy case ([#699])

- [ibc-relayer]
  - Replaced `rust-crypto` & `bitcoin-wallet` deprecated dependencies ([#352])
  - Fix for hard-coded account number ([#752])
  - Fix for chains that don't have `cosmos` account prefix ([#416])
  - Fix for building the `trusted_validator_set` for the header used in client updates ([#770])
  - Don't send `MsgAcknowledgment` if channel is closed ([#675])
  - Fix a bug where the keys addresses had their account prefix overriden by the prefix in the configuration ([#751])

- [ibc-relayer-cli]
  - Hermes guide: improved installation guideline ([#672])
  - Make fee denom and amount configurable ([#754])

- [ibc-proto]
  - Fix for proto files re-compilation bug ([#801])

### BREAKING CHANGES

- [ibc]
  - `MsgConnectionOpenAck.counterparty_connection_id` is now a `ConnectionId` instead of an `Option<ConnectionId>`([#700])

- [ibc-relayer]
  - Remove the light client configuration from the global configuration ([#793])

- [ibc-relayer-cli]
    - Remove the light add and light rm commands ([#793])


[#352]: https://github.com/informalsystems/ibc-rs/issues/352
[#362]: https://github.com/informalsystems/ibc-rs/issues/362
[#357]: https://github.com/informalsystems/ibc-rs/issues/357
[#416]: https://github.com/informalsystems/ibc-rs/issues/416
[#561]: https://github.com/informalsystems/ibc-rs/issues/561
[#550]: https://github.com/informalsystems/ibc-rs/issues/550
[#599]: https://github.com/informalsystems/ibc-rs/issues/599
[#630]: https://github.com/informalsystems/ibc-rs/issues/630
[#632]: https://github.com/informalsystems/ibc-rs/issues/632
[#640]: https://github.com/informalsystems/ibc-rs/issues/640
[#672]: https://github.com/informalsystems/ibc-rs/issues/672
[#673]: https://github.com/informalsystems/ibc-rs/issues/673
[#675]: https://github.com/informalsystems/ibc-rs/issues/675
[#685]: https://github.com/informalsystems/ibc-rs/issues/685
[#689]: https://github.com/informalsystems/ibc-rs/issues/689
[#695]: https://github.com/informalsystems/ibc-rs/issues/695
[#699]: https://github.com/informalsystems/ibc-rs/issues/699
[#700]: https://github.com/informalsystems/ibc-rs/pull/700
[#715]: https://github.com/informalsystems/ibc-rs/issues/715
[#734]: https://github.com/informalsystems/ibc-rs/issues/734
[#736]: https://github.com/informalsystems/ibc-rs/issues/736
[#740]: https://github.com/informalsystems/ibc-rs/issues/740
[#748]: https://github.com/informalsystems/ibc-rs/issues/748
[#751]: https://github.com/informalsystems/ibc-rs/issues/751
[#752]: https://github.com/informalsystems/ibc-rs/issues/752
[#754]: https://github.com/informalsystems/ibc-rs/issues/754
[#761]: https://github.com/informalsystems/ibc-rs/issues/761
[#772]: https://github.com/informalsystems/ibc-rs/issues/772
[#770]: https://github.com/informalsystems/ibc-rs/issues/770
[#793]: https://github.com/informalsystems/ibc-rs/pull/793
[#798]: https://github.com/informalsystems/ibc-rs/issues/798
[#801]: https://github.com/informalsystems/ibc-rs/issues/801
[#805]: https://github.com/informalsystems/ibc-rs/issues/805
[#806]: https://github.com/informalsystems/ibc-rs/issues/806
[#809]: https://github.com/informalsystems/ibc-rs/issues/809


## v0.1.1
*February 17, 2021*

This release brings a quick fix for a problem with a dependency of crate
`ibc-relayer`, which causes build & installation issues. Many thanks to
@Fraccaman for bringing this problem to our attention! ([#672])


Additionally, this release also introduces initial implementation for most of
ICS 004 handlers, and several bug fixes and improvements, e.g., refactored
some CLI code, refactored the Height type in the IBC Events, and a bug fix
involving packet acks in a 3-chain setup. More details below.

### FEATURES
- [ibc-relayer]
  - Listen to channel close initialization event and perform the close handshake ([#560])
  - Updated to tendermint-rs `v0.18.1` ([#682], [#671])

### IMPROVEMENTS

- [ibc]
  - Change event height to ICS height ([#549])

- [ibc-relayer-cli]
  - Cleanup CLI code ([#572])

### BUG FIXES

- [ibc]
  - Fix panic in conn open try when no connection id is provided ([#626])
  - Disable MBT tests if the "mocks" feature is not enabled ([#643])

- [ibc-relayer]
  - Quick fix for `funty` breaking change bug ([#665])

- [ibc-relayer-cli]
  - Fix wrong acks sent with `tx raw packet-ack` in a 3-chain setup ([#614])

### BREAKING CHANGES

- [ibc]
  - Implementation of the `ChanOpenAck`, `ChanOpenConfirm`, `ChanCloseInit`, and `ChanCloseConfirm` handlers ([#316])
  - Remove dependency on `tendermint-rpc` ([#624])

- [ibc-relayer-cli]
  - Remove the `proof` option from CLI ([#572])

[#316]: https://github.com/informalsystems/ibc-rs/issues/316
[#549]: https://github.com/informalsystems/ibc-rs/issues/549
[#560]: https://github.com/informalsystems/ibc-rs/issues/560
[#572]: https://github.com/informalsystems/ibc-rs/issues/572
[#614]: https://github.com/informalsystems/ibc-rs/issues/614
[#622]: https://github.com/informalsystems/ibc-rs/issues/622
[#624]: https://github.com/informalsystems/ibc-rs/issues/624
[#626]: https://github.com/informalsystems/ibc-rs/issues/626
[#637]: https://github.com/informalsystems/ibc-rs/issues/637
[#643]: https://github.com/informalsystems/ibc-rs/issues/643
[#665]: https://github.com/informalsystems/ibc-rs/issues/665
[#671]: https://github.com/informalsystems/ibc-rs/pull/671
[#682]: https://github.com/informalsystems/ibc-rs/issues/682

[ibc]: https://github.com/informalsystems/ibc-rs/tree/master/modules
[ibc-relayer-cli]: https://github.com/informalsystems/ibc-rs/tree/master/relayer-cli

## v0.1.0
*February 4, 2021*

🎉 This release brings the first publication of `ibc-relayer` and
`ibc-relayer-cli` to [crates.io](https://crates.io).

Noteworthy changes in this release include:

- The binary in the `ibc-relayer-cli` crate was given the name Hermes.
- We published a comprehensive guide for Hermes at [hermes.informal.systems](https://hermes.informal.systems).
- Major improvements to user experience, in particular at CLI level: JSON output,
  configurable log output level, dedicated channel handshake command, as well as
  overall improvements to error display and output.

### FEATURES

- Continous Integration (CI) end-to-end (e2e) testing with gaia v4 ([#32], [#582], [#602])
- Add support for streamlining releases ([#507])

- [ibc-relayer-cli]
  - Implement command to query the channels associated with a connection ([#505])
  - JSON output for queries and txs ([#500])
  - Added 'required' annotation for CLIs queries & txs; better error display ([#555])
  - Implement commands for channel close init and confirm ([#538])
  - Implement command to perform the handshake for a new channel ([#557])
  - Query all clients command ([#552])
  - Query all connections command ([#553])
  - Query all channels command ([#568])
  - Added a relayer binary guide ([#542])
  - Split the dev-env script in `setup_chains` and `init_clients` ([#577])

- [ibc-relayer]
  - Added retry mechanism, restructured relayer ([#519])
  - Relay `MsgTimeoutOnClose` if counterparty channel state is `State::Closed`

- [ibc]
  - Add `MsgTimeoutOnClose` message type ([#563])
  - Implement `MsgChannelOpenTry` message handler ([#543])

### IMPROVEMENTS

- Update to `tendermint-rs` v0.18.0 ([#517], [#583])
- Update to `tokio` 1.0, `prost` 0.7 and `tonic` 0.4 ([#527])

- [ibc-relayer-cli]
  - Replace `ChannelConfig` in `Channel::new` ([#511])
  - Add `packet-send` CLI ([#470])
  - UX improvements for relayer txs ([#536], [#540], [#554])
  - Allow running standalone commands concurrently to the main relayer loop ([#501])
  - Remove the simd-based integration tests ([#593])

- [ibc-relayer]
  - Performance improvements ([#514], [#537])
  - Fix for mismatching `bitcoin` dep ([#525])

- [ibc]
  - Clean the `validate_basic` method ([#94])
  - `MsgConnectionOpenAck` testing improvements ([#306])

### BUG FIXES:
- [ibc-relayer-cli]
  - Help and usage commands show 'hermes' for executable name ([#590])

- [ibc]
  - Fix for storing `ClientType` upon 'create-client' ([#513])

### BREAKING CHANGES:

- [ibc]
  - The `ibc::handler::Event` is removed and handlers now produce `ibc::events::IBCEvent`s ([#535])

[#32]: https://github.com/informalsystems/ibc-rs/issues/32
[#94]: https://github.com/informalsystems/ibc-rs/issues/94
[#306]: https://github.com/informalsystems/ibc-rs/issues/306
[#470]: https://github.com/informalsystems/ibc-rs/issues/470
[#500]: https://github.com/informalsystems/ibc-rs/issues/500
[#501]: https://github.com/informalsystems/ibc-rs/issues/501
[#505]: https://github.com/informalsystems/ibc-rs/issues/505
[#507]: https://github.com/informalsystems/ibc-rs/issues/507
[#511]: https://github.com/informalsystems/ibc-rs/pull/511
[#513]: https://github.com/informalsystems/ibc-rs/issues/513
[#514]: https://github.com/informalsystems/ibc-rs/issues/514
[#517]: https://github.com/informalsystems/ibc-rs/issues/517
[#519]: https://github.com/informalsystems/ibc-rs/issues/519
[#525]: https://github.com/informalsystems/ibc-rs/issues/525
[#527]: https://github.com/informalsystems/ibc-rs/issues/527
[#535]: https://github.com/informalsystems/ibc-rs/issues/535
[#536]: https://github.com/informalsystems/ibc-rs/issues/536
[#537]: https://github.com/informalsystems/ibc-rs/issues/537
[#538]: https://github.com/informalsystems/ibc-rs/issues/538
[#540]: https://github.com/informalsystems/ibc-rs/issues/540
[#542]: https://github.com/informalsystems/ibc-rs/issues/542
[#543]: https://github.com/informalsystems/ibc-rs/issues/543
[#552]: https://github.com/informalsystems/ibc-rs/issues/553
[#553]: https://github.com/informalsystems/ibc-rs/issues/553
[#554]: https://github.com/informalsystems/ibc-rs/issues/554
[#555]: https://github.com/informalsystems/ibc-rs/issues/555
[#557]: https://github.com/informalsystems/ibc-rs/issues/557
[#563]: https://github.com/informalsystems/ibc-rs/issues/563
[#568]: https://github.com/informalsystems/ibc-rs/issues/568
[#577]: https://github.com/informalsystems/ibc-rs/issues/577
[#582]: https://github.com/informalsystems/ibc-rs/issues/582
[#583]: https://github.com/informalsystems/ibc-rs/issues/583
[#590]: https://github.com/informalsystems/ibc-rs/issues/590
[#593]: https://github.com/informalsystems/ibc-rs/issues/593
[#602]: https://github.com/informalsystems/ibc-rs/issues/602

## v0.0.6
*December 23, 2020*

This release focuses on upgrading the relayer and ibc modules to the latest interfaces from the ecosystem:
tendermint-rs `v0.17`, which brings the protobuf changes from tendermint `v0.34.0`, plus alignment with
the latest cosmos proto versions from `v0.40.0-rc5` (sometimes called 'stargate-5').

### FEATURES
- Update to tendermint-rs version `0.17` ([#451])
- Update to cosmos-sdk IBC proto version `v0.40.0-rc5` ([#451])

- [ibc-relayer]

- [ibc-relayer-cli]
  - Packet CLIs for recv_packet ([#443])
  - Packet CLIs for acknowledging packets ([#468])

### IMPROVEMENTS
- [ibc-relayer]
  - Mock chain (implementing IBC handlers) and integration against CLI ([#158])
  - Relayer tests for client update (ping pong) against MockChain ([#381])
  - Relayer refactor to improve testing and add semantic dependencies ([#447])

[#158]: https://github.com/informalsystems/ibc-rs/issues/158
[#379]: https://github.com/informalsystems/ibc-rs/issues/379
[#381]: https://github.com/informalsystems/ibc-rs/issues/381
[#443]: https://github.com/informalsystems/ibc-rs/issues/443
[#447]: https://github.com/informalsystems/ibc-rs/issues/447
[#451]: https://github.com/informalsystems/ibc-rs/issues/451
[#468]: https://github.com/informalsystems/ibc-rs/issues/468


## v0.0.5
*December 2, 2020*

This release focuses on implementing relayer and relayer-cli functionality towards a full v0 implementation.
We now have the full-stack implementation for supporting client creation & updates, as well as connection- and channel handshakes.
We also consolidated our TLA+ specs into an "IBC Core TLA+ specification," and added ICS 020 spec.

Special thanks to external contributors for this release: @CharlyCst ([#347], [#419]).

- [ibc-relayer-cli]
  - Add `--all` option to `light rm` command to remove all peers for a given chain ([#431])

[#431]: https://github.com/informalsystems/ibc-rs/issues/431

### FEATURES

- Update to tendermint-rs version `0.17-RC3` ([#403])
- [changelog] Added "unreleased" section in `CHANGELOG.MD` to help streamline releases ([#274])
- [ibc]
    - Implement flexible connection id selection ([#332])
    - ICS 4 Domain Types for channel handshakes and packets ([#315], [#95])
    - Introduce LightBlock support for MockContext ([#389])
- [ibc-relayer]
    - Retrieve account sequence information from a chain using a GRPC client (#337)
    - Implementation of chain runtime for v0 ([#330])
    - Integrate relayer spike into ibc-relayer crate ([#335])
    - Implement `query_header_at_height` via plain RPC queries (no light client verification) ([#336])
    - Implement the relayer logic for connection handshake messages ([#358], [#359], [#360])
    - Implement the relayer logic for channel handshake messages ([#371], [#372], [#373], [#374])
- [ibc-relayer-cli]
    - Merge light clients config in relayer config and add commands to add/remove light clients ([#348])
    - CLI for client update message ([#277])
    - Implement the relayer CLI for connection handshake messages ([#358], [#359], [#360])
    - Implement the relayer CLI for channel handshake messages ([#371], [#372], [#373], [#374])
    - Added basic client, connection, and channel lifecyle in relayer v0 ([#376], [#377], [#378])
    - Implement commands to add and list keys for a chain ([#363])
    - Allow overriding of peer_id, height and hash in light add command ([#428])
- [proto-compiler]
    - Refactor and allow specifying a commit at which the Cosmos SDK should be checked out ([#366])
    - Add a `--tag` option to the `clone-sdk` command to check out a tag instead of a commit ([#369])
    - Fix `--out` command line parameter (instead of `--path`) ([#419])
- [ibc/relayer-spec]
    - ICS 020 spec in TLA+ ([#386])
    - Prepare IBC Core TLA+ specs ([#404])

### IMPROVEMENTS

- [ibc-relayer]
    - Pin chain runtime against Tokio 0.2 by downgrading for 0.3 to avoid dependency hell ([#415], follow up to [#402])
- [ibc-relayer-cli]
    - Split tasks spawned by CLI commands into their own modules ([#331])
    - V0 command implementation ([#346])
- [ibc]
    - Split `msgs.rs` of ICS002 in separate modules ([#367])
    - Fixed inconsistent versioning for ICS003 and ICS004 ([#97])
    - Fixed `get_sign_bytes` method for messages ([#98])
    - Homogenize ConnectionReader trait so that all functions return owned objects ([#347])
    - Align with tendermint-rs in the domain type definition of `block::Id` ([#338])


[#95]: https://github.com/informalsystems/ibc-rs/issues/95
[#97]: https://github.com/informalsystems/ibc-rs/issues/97
[#98]: https://github.com/informalsystems/ibc-rs/issues/98
[#274]: https://github.com/informalsystems/ibc-rs/issues/274
[#277]: https://github.com/informalsystems/ibc-rs/issues/277
[#315]: https://github.com/informalsystems/ibc-rs/issues/315
[#330]: https://github.com/informalsystems/ibc-rs/issues/330
[#332]: https://github.com/informalsystems/ibc-rs/issues/332
[#335]: https://github.com/informalsystems/ibc-rs/pull/335
[#336]: https://github.com/informalsystems/ibc-rs/issues/336
[#337]: https://github.com/informalsystems/ibc-rs/issues/337
[#338]: https://github.com/informalsystems/ibc-rs/issues/338
[#346]: https://github.com/informalsystems/ibc-rs/issues/346
[#347]: https://github.com/informalsystems/ibc-rs/issues/347
[#348]: https://github.com/informalsystems/ibc-rs/pull/348
[#358]: https://github.com/informalsystems/ibc-rs/issues/358
[#359]: https://github.com/informalsystems/ibc-rs/issues/359
[#360]: https://github.com/informalsystems/ibc-rs/issues/360
[#363]: https://github.com/informalsystems/ibc-rs/issues/363
[#366]: https://github.com/informalsystems/ibc-rs/issues/366
[#367]: https://github.com/informalsystems/ibc-rs/issues/367
[#368]: https://github.com/informalsystems/ibc-rs/issues/368
[#369]: https://github.com/informalsystems/ibc-rs/pull/369
[#371]: https://github.com/informalsystems/ibc-rs/issues/371
[#372]: https://github.com/informalsystems/ibc-rs/issues/372
[#373]: https://github.com/informalsystems/ibc-rs/issues/373
[#374]: https://github.com/informalsystems/ibc-rs/issues/374
[#376]: https://github.com/informalsystems/ibc-rs/issues/376
[#377]: https://github.com/informalsystems/ibc-rs/issues/377
[#378]: https://github.com/informalsystems/ibc-rs/issues/378
[#386]: https://github.com/informalsystems/ibc-rs/issues/386
[#389]: https://github.com/informalsystems/ibc-rs/issues/389
[#402]: https://github.com/informalsystems/ibc-rs/issues/402
[#403]: https://github.com/informalsystems/ibc-rs/issues/403
[#404]: https://github.com/informalsystems/ibc-rs/issues/404
[#419]: https://github.com/informalsystems/ibc-rs/issues/419
[#415]: https://github.com/informalsystems/ibc-rs/issues/415
[#428]: https://github.com/informalsystems/ibc-rs/issues/428
[changelog]: https://github.com/informalsystems/ibc-rs/tree/master/CHANGELOG.md
[proto-compiler]: https://github.com/informalsystems/ibc-rs/tree/master/proto-compiler

## v0.0.4
*October 19, 2020*

This release focuses on alignment with the Cosmos ecosystem: adaptations to Tendermint-rs 0.16 and subsequently to 0.17 (`0.17.0-rc1`), and numerous protobuf updates following latest stargate releases.

Additional highlights:
- Adding DomainTypes and (de)serialization capability to ICS02 and ICS03 messages and structures.
- Improvements of the IBC message processor framework (handlers, contexts and mocks).
- Added initial implementations for the ICS26 (routing module) and ICS18 (basic relayer algorithms module) for use in testing.
- Also added support for packet handling in the relayer algorithm specifications.

### BREAKING CHANGES:
- [ibc-relayer] & [ibc] Alignment with ecosystem updates:
    - Compatibility with the latest protobuf (Gaia stargate-3 and stargate-4) ([#191], [#272], [#273], [#278])
    - Adaptations to tendermint 0.17 ([#286], [#293], [#300], [#302], [#308])
- [ibc-relayer] UX improvement: Remove proof option from client connections command ([#205])

### FEATURES:
- [ibc/ics03] ICS03 Ack and Confirm message processors ([#223])
- [ibc-relayer-cli]
    - Relayer CLIs for client messages ([#207])
    - Relayer CLIs for connection-open-init ([#206])
    - Queries for consensus state and client state ([#149], [#150])
- [ibc] Routing module minimal implementation for MVP ([#159], [#232])
- [ibc/relayer-spec] Relayer specification for packet handling ([#229], [#234], [#237])
- [ibc/relayer-spec] Basic packet handling in TLA+([#124])
- [ibc] Basic relayer functionality: a test with ClientUpdate ping-pong between two mocked chains ([#276])

### IMPROVEMENTS:
- [ibc] Implemented the `DomainType` trait for IBC proto structures ([#245], [#249]).
- [ibc] & [ibc-proto] Several improvements to message processors, among which ([#218]):
    - ICS03 connection handshake protocol initial implementation and tests ([#160])
    - Add capability to decode from protobuf Any* type into Tendermint and Mock client states
    - Cleanup Any* client wrappers related code
    - Migrate handlers to newer protobuf definitions ([#226])
    - Extend client context mock ([#221])
    - Context mock simplifications and cleanup ([#269], [#295], [#296], [#297])
- [ibc/ics03] Split `msgs.rs` in multiple files, implement `From` for all messages ([#253])
- [ibc-proto]
    - Move ibc-proto source code into ibc-rs ([#142]) and fixed code deduplication ([#282], [#284])
    - Consolidate proto-compiler logic [#241]
- [ibc/relayer-spec] Add support for APALACHE to the Relayer TLA+ spec ([#165])
- [ibc-relayer] Update to tendermint v.0.16 and integrate with the new light client implementation ([#90], [#243])

### BUG FIXES:
- [ibc] Removed "Uninitialized" state from connection ([#217])
- [ibc-relayer-cli] Fix for client query subcommands ([#231])
- [disclosure-log] & [spec/connection-handshake] Disclosed bugs in ICS3 version negotiation and proposed a fix ([#209], [#213])

[#90]: https://github.com/informalsystems/ibc-rs/issues/90
[#124]: https://github.com/informalsystems/ibc-rs/issues/124
[#142]: https://github.com/informalsystems/ibc-rs/issues/142
[#149]: https://github.com/informalsystems/ibc-rs/issues/149
[#150]: https://github.com/informalsystems/ibc-rs/issues/150
[#159]: https://github.com/informalsystems/ibc-rs/issues/159
[#160]: https://github.com/informalsystems/ibc-rs/issues/160
[#165]: https://github.com/informalsystems/ibc-rs/issues/165
[#191]: https://github.com/informalsystems/ibc-rs/issues/191
[#205]: https://github.com/informalsystems/ibc-rs/issues/205
[#206]: https://github.com/informalsystems/ibc-rs/issues/206
[#207]: https://github.com/informalsystems/ibc-rs/issues/207
[#209]: https://github.com/informalsystems/ibc-rs/issues/209
[#213]: https://github.com/informalsystems/ibc-rs/issues/213
[#217]: https://github.com/informalsystems/ibc-rs/issues/217
[#218]: https://github.com/informalsystems/ibc-rs/issues/218
[#221]: https://github.com/informalsystems/ibc-rs/issues/221
[#223]: https://github.com/informalsystems/ibc-rs/issues/223
[#226]: https://github.com/informalsystems/ibc-rs/issues/226
[#229]: https://github.com/informalsystems/ibc-rs/issues/229
[#231]: https://github.com/informalsystems/ibc-rs/issues/231
[#232]: https://github.com/informalsystems/ibc-rs/issues/232
[#234]: https://github.com/informalsystems/ibc-rs/issues/234
[#237]: https://github.com/informalsystems/ibc-rs/issues/237
[#241]: https://github.com/informalsystems/ibc-rs/issues/241
[#243]: https://github.com/informalsystems/ibc-rs/issues/243
[#245]: https://github.com/informalsystems/ibc-rs/issues/245
[#249]: https://github.com/informalsystems/ibc-rs/issues/249
[#253]: https://github.com/informalsystems/ibc-rs/issues/253
[#269]: https://github.com/informalsystems/ibc-rs/issues/269
[#272]: https://github.com/informalsystems/ibc-rs/issues/272
[#273]: https://github.com/informalsystems/ibc-rs/issues/273
[#276]: https://github.com/informalsystems/ibc-rs/issues/276
[#278]: https://github.com/informalsystems/ibc-rs/issues/278
[#282]: https://github.com/informalsystems/ibc-rs/issues/282
[#284]: https://github.com/informalsystems/ibc-rs/issues/284
[#286]: https://github.com/informalsystems/ibc-rs/issues/286
[#293]: https://github.com/informalsystems/ibc-rs/issues/293
[#295]: https://github.com/informalsystems/ibc-rs/issues/295
[#296]: https://github.com/informalsystems/ibc-rs/issues/296
[#297]: https://github.com/informalsystems/ibc-rs/issues/297
[#300]: https://github.com/informalsystems/ibc-rs/issues/300
[#302]: https://github.com/informalsystems/ibc-rs/issues/302
[#308]: https://github.com/informalsystems/ibc-rs/issues/308
[ibc-proto]: https://github.com/informalsystems/ibc-rs/tree/master/proto
[disclosure-log]: https://github.com/informalsystems/ibc-rs/blob/master/docs/disclosure-log.md
[spec/connection-handshake]: https://github.com/informalsystems/ibc-rs/tree/master/docs/spec/connection-handshake
[ibc-relayer]: https://github.com/informalsystems/ibc-rs/tree/master/relayer

## v0.0.3
*September 1, 2020*

This release focuses on the IBC message processor framework and initial
implementations in ICS02 and ICS07. It also introduces an initial specification for the relayer algorithm.

Other highlights:
- The ibc crate is published as [ibc](https://crates.io/crates/ibc) in crates.io
- ADR-001 and ADR-003 are complete. 🎉

### BREAKING CHANGES:
- [ibc] Renamed `modules` crate to `ibc` crate. Version number for the new crate is not reset. ([#198])
- [ibc/ics02] `ConnectionId`s are now decoded to `Vec<ConnectionId>` and validated instead of `Vec<String>` ([#185])
- [ibc/ics03] Removed `Connection` and `ConnectionCounterparty` traits ([#193])
- [ibc/ics04] Removed `Channel` and `ChannelCounterparty` traits ([#192])

### FEATURES:
- [ibc/ics02] partial implementation of message handler ([#119], [#194])
- [ibc/ics07] partial implementation of message handler ([#119], [#194])
- [architecture/ADR-003] Proposal for IBC handler (message processor) architecture ([#119], [#194])
- [ibc/relayer-spec] Detailed technical specification of the relayer algorithm with focus on client update ([#84])
- [architecture/ADR-001] Documentation for the repository structure ([#1])
- [architecture/FSM-1] Connection Handshake FSM English description ([#122])

### IMPROVEMENTS:
- [contributing] Updated CONTRIBUTING.md. Please read before opening PRs ([#195])
- [ibc-relayer-cli] Refactor ConnectionId decoding in `query client` ([#185])

### BUG FIXES:
- [ibc/ics24] Identifiers limit update according to ICS specs ([#168])

[ibc/relayer-spec]: https://github.com/informalsystems/ibc-rs/blob/master/docs/spec/relayer/Relayer.md
[#84]: https://github.com/informalsystems/ibc-rs/issues/84
[architecture/ADR-001]: https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-001-repo.md
[#1]: https://github.com/informalsystems/ibc-rs/issues/1
[contributing]: https://github.com/informalsystems/ibc-rs/blob/master/CONTRIBUTING.md
[#195]: https://github.com/informalsystems/ibc-rs/pull/195
[ibc]: https://github.com/informalsystems/ibc-rs/tree/master/modules
[#198]: https://github.com/informalsystems/ibc-rs/issues/198
[ibc/ics02]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/core/ics02_client
[#185]: https://github.com/informalsystems/ibc-rs/issues/185
[ibc/ics03]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/core/ics03_connection
[#193]: https://github.com/informalsystems/ibc-rs/issues/193
[ibc/ics04]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/core/ics04_channel
[#192]: https://github.com/informalsystems/ibc-rs/issues/192
[ibc-relayer-cli]: https://github.com/informalsystems/ibc-rs/tree/master/relayer-cli
[architecture/FSM-1]: https://github.com/informalsystems/ibc-rs/blob/v0.1.0/docs/architecture/fsm-async-connection.md
[#122]: https://github.com/informalsystems/ibc-rs/issues/122
[architecture/ADR-003]: https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-003-handler-implementation.md
[#119]: https://github.com/informalsystems/ibc-rs/issues/119
[#194]: https://github.com/informalsystems/ibc-rs/issues/194
[ibc/ics24]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/core/ics24_host
[#168]: https://github.com/informalsystems/ibc-rs/issues/168
[ibc/ics07]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/clients/ics07_tendermint

## v0.0.2

*August 1, 2020*

This release is focused on updating the query system from amino to protobuf,
implementing a few queries from the CLI, and establishing an initial testing framework
that will support multiple chain types.

It does not target a stable release of Cosmos-SDK chains, but is tracking
the latest state of development towards the Cosmos-SDK Stargate release.

### BREAKING CHANGES:

- [ibc|ibc-relayer] Refactor queries, paths, and Chain trait to reduce code and use
  protobuf instead of Amino.
        [\#152](https://github.com/informalsystems/ibc-rs/pull/152),
        [\#174](https://github.com/informalsystems/ibc-rs/pull/174),
        [\#155](https://github.com/informalsystems/ibc-rs/pull/155)
- [repo] Moved relayer/cli to relayer-cli, relayer/relay to relayer. [\#183](https://github.com/informalsystems/ibc-rs/pull/183)

### FEATURES:

- [ibc-relayer] Query connections given client id. [\#169](https://github.com/informalsystems/ibc-rs/pull/169)
- [ibc-relayer] Query connection given connection id. [\#136](https://github.com/informalsystems/ibc-rs/pull/136)
- [ibc-relayer] Query channel given channel id and port [\#163](https://github.com/informalsystems/ibc-rs/pull/163)
- [spec] Channel closing datagrams in TLA+ [\#141](https://github.com/informalsystems/ibc-rs/pull/141)

### IMPROVEMENTS:

- [ci] Framework (scripts and Github Actions) for integration testing the relayer queries against
    the Cosmos-SDK's `simd` binary with prepopulated IBC state in the genesis
        [\#140](https://github.com/informalsystems/ibc-rs/pull/140),
        [\#184](https://github.com/informalsystems/ibc-rs/pull/184)
- [ibc-relayer|ibc] Implemented better Raw type handling. [\#156](https://github.com/informalsystems/ibc-rs/pull/156)
- [repo] Add rust-toolchain file. [\#154](https://github.com/informalsystems/ibc-rs/pull/154)

### BUG FIXES:

- [ibc] Fixed the identifiers limits according to updated ics spec. [\#189](https://github.com/informalsystems/ibc-rs/pull/189)
- [ibc/relayer] Remove some warnings triggered during compilation due to dependency specification. [\#132](https://github.com/informalsystems/ibc-rs/pull/132)
- [ibc] Fix nightly runs. [\#161](https://github.com/informalsystems/ibc-rs/pull/161)
- [repo] Fix for incomplete licence terms. [\#153](https://github.com/informalsystems/ibc-rs/pull/153)

## 0.0.1

*July 1st, 2020*

This is the initial prototype release of an IBC relayer and TLA+ specifications.
There are no compatibility guarantees until v0.1.0.

Includes:

- Configuration file definition and validation
- Client state, consensus state, connection, channel queries.
    - Note: deserialization is unimplemented as it has dependency on migration to protobuf for ABCI queries
- Per chain light clients threads are created and headers are periodically retrieved and verified.
- Per chain IBC event monitor threads are spawned and main event handler that receives them.
    - Note: the event handler just displays the events.
- IBC Modules partial implementation for datastructures, messages and queries.
- Some English and TLA+ specifications for Connection & Channel Handshake as well as naive relayer algorithm.
