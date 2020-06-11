# ADR 001: Repository Structure

## Changelog

* 2020-06-11: First draft.

## Context

This crate comprises a Rust implementation of the [IBC](https://github.com/cosmos/ics) protocol.
The Rust implementation is supported by specifications, which are primarily written in TLA+, and sometimes in English.

At the moment we are invested mostly in the development of a relayer and several important modules (client, connection, channel, and packets).
Eventually, we hope to cover the full IBC suite.

## Decision


The structure of the `ibc-rs` repository comprise three broad parts:

1. The codebase for the IBC relayer implementation is in `relayer`;
2. The codebase for IBC modules is in `modules`;
3. English and TLA+ specs reside under `docs/spec`.

### References

The following resources serve as references implementations or specifications that we use to guide the development of the present crate:

For the IBC relayer:

- A first implementation of the IBC relayer in Golang is under active development at [iqlusioninc/relayer](https://github.com/iqlusioninc/relayer).
- The English specification of the relayer algorithm is captured in the [ICS018](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms) spec.

For IBC modules:

- A Golang implementation of IBC modules is under active development as part of the Cosmos SDK, at [cosmos/cosmos-sdk/x/ibc](https://github.com/cosmos/cosmos-sdk/tree/master/x/ibc).
- The English specifications for IBC modules reside in [cosmos/ics](https://github.com/cosmos/ics/tree/master/spec).

## Status

Proposed

## Consequences

Not applicable.