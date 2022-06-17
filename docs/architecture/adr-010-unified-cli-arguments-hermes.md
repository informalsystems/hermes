# ADR 010: Unified approach for CLI arguments for Hermes v1.0.0

## Changelog
* 15.06.2022: Proposed.

## Context

In this ADR we provide recommendations and intuitions to using flags for all the arguments of the Hermes commands.

The problem we are trying to solve is a unified approach to CLI arguments for Hermes v1.0.0.

## Decision

To avoid confusion, all the parameters should take long flags. The following approach should be applied:

* Only long flags are used in order to avoid having nonintuitive flags or conflicting flags.
* Any parameter ending with `_id` should have the `_id` removed from the flag to shorten it. For example the flag for `chain_id` should only be `chain`.
* Flags which can be shortened and still be meaningful should be shortened. This is done for `connection`, `channel` and `sequence`, which become respectively `conn`, `chan` and `seq`.
* For the channel and connection creation CLIs, the objects at the two ends are prefixed by `--a-` and `--b-`. Example `--a-chain` and `--b-chain`.
* Whenever `chain`, `conn`, `chan` and `port` flags have to be disambiguated with a specifier, the specifier will be a prefix. Example of specifiers we currently use are `host`, `reference`, `a`, `b` and `counterparty`.

The following commands are implemented, with the binary name `hermes` often omitted:

### Hermes global flags

* `hermes --config <CONFIG> <COMMAND>`

* `hermes --json <COMMAND>`

### Commands for clients

* `create client --host-chain <HOST_CHAIN_ID> --reference-chain <REFERENCE_CHAIN_ID>`
    * Optional: `[--clock-drift <CLOCK_DRIFT>] [--trust-threshold <TRUST_THRESHOLD>] [--trusting-period <TRUSTING_PERIOD>]`

* `update client --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--height <REFERENCE_HEIGHT>] [--trusted-height <REFERENCE_TRUSTED_HEIGHT>]`

* `upgrade client --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>`

* `upgrade clients --reference-chain <REFERENCE_CHAIN_ID>`
    * Optional: `[--host-chain <HOST_CHAIN_ID>]`

### Create a connection

* `create connection --a-chain <A_CHAIN_ID> --b-chain <B_CHAIN_ID>`
    * Optional: `[--delay <DELAY>]`

* `create connection --a-chain <A_CHAIN_ID> --a-client <A_CLIENT_ID> --b-client <B_CLIENT_ID>`
    * Optional: `[--delay <DELAY>]`

### Create a channel

* `create channel --a-chain <A_CHAIN_ID> --a-conn <A_CONNECTION_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID>`
    * Optional: `[--chan-version <VERSION>] [--order <ORDER>]`

* `create channel --a-chain <A_CHAIN_ID> --b-chain <B_CHAIN_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID> --new-client-conn`
    * Optional: `[--chan-version <VERSION>] [--order <ORDER>]`

### Commands for keys

* `keys add --chain <CHAIN_ID> --key-file <KEY_FILE> --mnemonic-file <MNEMONIC_FILE>`
    * Optional: `[--hd-path <HD_PATH>] [--key-name <KEY_NAME>]`

* `keys balance --chain <CHAIN_ID>`
    * Optional: `[--key-name <KEY_NAME>]`

* `keys delete --chain <CHAIN_ID> --all`

* `keys delete --chain <CHAIN_ID> --key-name <KEY_NAME>`

* `keys list --chain <CHAIN_ID>`

### Listen

* `listen --chain <CHAIN_ID>`
    * Optional: `[--event <EVENT>]`

### Misbehaviour

* `misbehaviour --chain <CHAIN_ID> --client <CLIENT_ID>`

### Start the relayer in multi-chain mode

* `start`
    * Optional: `[--full-scan]`

### Clear packets

* `clear packets --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

### Queries

__Client__

* `query client connections --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query client consensus --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--consensus-height <CONSENSUS_HEIGHT>] [--height <HEIGHT>] [--heights-only]`

* `query client header --chain <CHAIN_ID> --client <CLIENT_ID> --consensus-height <CONSENSUS_HEIGHT>`
    * Optional: `[--height <HEIGHT>]`

* `query client state --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query clients --host-chain <HOST_CHAIN_ID>`
    * Optional: `[--omit-chain-ids] [--reference-chain <REFERENCE_CHAIN_ID>]`

__Connection__

* `query connection channels --chain <CHAIN_ID> --conn <CONNECTION_ID>`

* `query connection end --chain <CHAIN_ID> --conn <CONNECTION_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query connections --chain <CHAIN_ID>`
    * Optional: `[--chain-counterparty <CHAIN_COUNTERPARTY_ID>] [--verbose]`

__Channel__

* `query channel client --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

* `query channel end --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query channel full --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`
    * Optional: `[--height <HEIGHT>] [--verbose]`

* `query channels --chain <CHAIN_ID>`
    * Optional: `[--counterparty-chain <COUNTERPARTY_CHAIN_ID>] [--verbose]`

__Packet__

* `query packet ack --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID> --seq <SEQUENCE>`
    * Optional: `[--height <HEIGHT>]`

* `query packet acks --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

* `query packet commitment --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID> --seq <SEQUENCE>`
    * Optional: `[--height <HEIGHT>]`

* `query packet commitments --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

* `query packet pending --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

* `query packet unreceived-acks --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

* `query packet unreceived-packets --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

__Tx__

* `query tx events --chain <CHAIN_ID> --hash <HASH>`

### Shell completion

* `completions --shell <SHELL>`

### Validate configuration file

* `config validate`

### Health check

* `health-check`

## Status

Proposed.

__17.06.22__

The following are not yet implemented:
* Optional flags for `upgrade clients`, issue [#2311](https://github.com/informalsystems/ibc-rs/issues/2311)
* Optional flags for `query connections`, issue [#2310](https://github.com/informalsystems/ibc-rs/issues/2310)
* Updating `query channel ends` to `query channel full`

The PR which updates the flags for all the commands as described in this ADR: [#2275](https://github.com/informalsystems/ibc-rs/pull/2275)

## Consequences

### Positive

* Clear parameters for Hermes commands

### Negative

* Breaking changes which will require updating anything using Hermes

### Neutral

## References

* Proposal in issue: [#2239](https://github.com/informalsystems/ibc-rs/issues/2239)