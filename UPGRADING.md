# Upgrading Hermes to a newer version

## v1.0.0-rc.0

> These instructions assume that you are running Hermes v0.15.0.
> If you are running an older version, please refer the corresponding
> in reverse chronological order to update to v0.15.0 first and then
> follow these instructions.

### Commands now use flags instead of positional arguments

From this version forward, all Hermes commands now use flags exclusively instead
of positional arguments.

For example, in version 0.15.0 the `create client` command would be invoked
as follows to create a client on host chain `ibc-0` which tracks reference chain `ibc-1`:

```
$ hermes create client ibc-0 ibc-1
````

As of version 1.0.0-rc.0, the command must now be invoked as follows, using flags instead of
positional arguments:

```
$ hermes create client --host-chain ibc-0 --reference-chain ibc-1
```

Please [consult the ADR][flags-adr] which describes the new CLI flags for all commands.

[flags-adr]: https://github.com/informalsystems/ibc-rs/blob/v1.0.0-rc.0/docs/architecture/adr-010-unified-cli-arguments-hermes.md

### The `keys restore` command has been merged into `keys add`

The `keys restore` command has been merged into the existing `keys add` command.

Restoring a key now takes a file containing the mnemonic as input instead of directly taking the mnemonic.

Additionally, the flag to specify the key name for the CLI command `keys add` has been changed from `--nname` to `--key-name`.

As of version 1.0.0-rc.0, one must use the `keys add` command as follows in order
to restore a key from a mnemonic file instead of the `keys restore` command:

```
$ hermes keys add -chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>
```

### The `gas_adjustment` setting has been deprecated in favor of `gas_multiplier`

The `gas_adjustment` setting has been deprecated in favor of new `gas_multiplier` setting.

If you were using the `gas_adjustment` setting, please remove it from the
chain configurations and use the `gas_multiplier` setting instead.

Whereas the `gas_adjustment` setting would specify a percentage by which to increase
the estimated gas amount before broadcasting a transaction (eg. a value of 0.1
would increase the gas by 10%), the `gas_multiplier` simply specifies by
which amount to multiply the estimated gas before sending a transaction.

For example, if the chain configuration used `gas_adjustment = 0.1` to increase
the estimated gas amount by 10%, you must now use `gas_multiplier = 1.1`.

### Two `query packet` commands have been renamed

The `query packet unreceived-packets` has been renamed to `query packet pending-sends` to better
reflect its behavior.

The `query packet unreceived-acks` has been renamed to `query packet pending-acks` for consistency.

## v0.15.0

No breaking changes from v0.14.1.

## v0.14.1

No breaking changes from v0.14.0.

## v0.14.0

This release notably features a new [`query packet pending`][pending] command to
list outstanding packet commitments that are either unreceived or pending
acknowledgement at both ends of a channel.

The `create channel` command now requires an existing client and connection,
unless the `--new-client-connection` flag is provided.
Please [refer to the guide][create-channel] for more information.

[ics-26]: https://github.com/cosmos/ibc/blob/master/spec/core/ics-026-routing-module/README.md
[pending]: https://hermes.informal.systems/commands/queries/packet.html#pending-packets
[create-channel]: http://hermes.informal.systems/commands/path-setup/channels.html#establish-channel


## Older versions

Please refer to the [CHANGELOG](CHANGELOG.md) for older versions.

