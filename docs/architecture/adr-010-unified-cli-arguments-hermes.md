# ADR 010: Unified approach for CLI arguments for Hermes v1.0.0

## Changelog
* 15.06.2022: Proposed.

## Context

In this ADR we provide recommendations and intuitions to using flags for all the arguments of the Hermes commands.

The problem we are trying to solve is a unified approach to CLI arguments for Hermes v1.0.0.

## Decision

To avoid confusion, all the parameters should take long flags. The following general scenarios should be applied:

* Only long flags are used in order to avoid having nonintuitive flags or conflicting flags.
* Any parameter ending with `_id` should have the `_id` removed from the flag to shorten it. For example the flag for `chain_id` should only be `chain`.
* Flags which can be shorten and still be meaningful should be shorten. This is done for `connection`, `channel` and `sequence`, which become respectively `conn`, `chan` and `seq`.
* In cases where there are source and destination parameters for a same object, the flags start with the prefix `--src-` and `--dst-`.
* In cases where there are undirectional parameters for a same object, the flags end with the suffix `-a` and `-b`.

The following commands are implemented, with the binary name `hermes` omitted:

### Hermes global flags

* `hermes --config <CONFIG> <COMMAND>`

* `hermes --json <COMMAND>`

### Commands for clients

* `create client --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID>`
    * Optional: `[--clock-drift <CLOCK_DRIFT>] [--trust-threshold <TRUST_THRESHOLD>] [--trusting-period <TRUSTING_PERDIOD>]`

* `update client --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--target-height <TARGET_HEIGHT>] [--trusted-height <TRUSTED_HEIGHT>]`

* `upgrade client --chain <DST_CHAIN_ID> --client <DST_CLIENT_ID>`

* `upgrade clients --chain <CHAIN_ID>`

### Create a connection

* `create connection --chain-a <CHAIN_A_ID> --chain-b <CHAIN_B_ID>`
    * Optional: `[--delay <DELAY>]`

* `create connection --chain-a <CHAIN_A_ID> --client-a <CLIENT_A_ID> --client-b <CLIENT_B_ID>`
    * Optional: `[--delay <DELAY>]`

### Create a channel

* `create channel --chain-a <CHAIN_A_ID> --chain-b <CHAIN_B_ID> --port-a <PORT_A_ID> --port-b <PORT_B_ID>`
    * Optional: `[--chan-version <VERSION>] [--new-client-conn] [--order <ORDER>]`

* `create channel --chain-a <CHAIN_A_ID> --conn-a <CONNECTION_A_ID> --port-a <PORT_A_ID> --port-b <PORT_B_ID>`
    * Optional: `[--chan-version <VERSION>] [--new-client-conn] [--order <ORDER>]`

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

### Clear objects

* `clear packets --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

### Queries

__Channel__

* `query channel client --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`

* `query channel end --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query channel ends --chain <CHAIN_ID> --port <PORT_ID> --chan <CHANNEL_ID>`
    * Optional: `[--height <HEIGHT>] [--verbose]`

* `query channels --chain <CHAIN_ID>`
    * Optional: `[--dst-chain <DST_CHAIN_ID>] [--verbose]`

__Client__

* `query client connections --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query client consensus --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--consensus-height <CONSENSUS_HEIGHT>] [--height <HEIGHT>] [--heights-only]`

* `query client header --chain <CHAIN_ID> --client <CLIENT_ID> --consensus-height <CONSENSUS_HEIGHT>`
    * Optional: `[--height <HEIGHT>]`

* `query client state --chain <CHAIN_ID> --client <CLIENT_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query clients --chain <CHAIN_ID>`
    * Optional: `[--omit-chain-ids] [--src-chain <ID>]`

__Connection__

* `query connection channels --chain <CHAIN_ID> --conn <CONNECTION_ID>`

* `query connection end --chain <CHAIN_ID> --conn <CONNECTION_ID>`
    * Optional: `[--height <HEIGHT>]`

* `query connections --chain <CHAIN_ID>`

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

Proposed

## Consequences

### Positive

* Clear parameters for Hermes commands

### Negative

* Breaking changes which will require updating anything using Hermes

### Neutral

## References

* Proposal in issue: [#2239](https://github.com/informalsystems/ibc-rs/issues/2239)