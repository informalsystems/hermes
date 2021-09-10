# Architecture

This document describes the architecture of ibc-rs. If you're looking for a high-level overview of the code base, you've come to the right place!

## Bird's Eye View

![](https://github.com/informalsystems/ibc-rs/blob/adi/arch/repo-context.pdf)

[What is it core reason developers use Hermes for?]

At its highest level, ibc-rs [does what?]

## Code Map 

This section talks briefly about the various directories and modules in ibc-rs. 

### `modules`

The main data structures and on-chain logic of the IBC protocol.

### `relayer`

Provides the logic for relaying datagrams between chains. 

### `relayer-cli`

A CLI wrapper around the `relayer` library, which exposes the Hermes binary.

### `relayer-rest`

REST server utilized by the Hermes IBC relayer.

### `proto`

Consists of Rust types generated from proto definitions necessary for interacting with the Cosmos SDK. 

### `proto-compiler`

CLI tool to automate the compilation of proto buffers. 

### `telemetry`

Used by Hermes to gather telemetry data and expose it via a Prometheus endpoint.

## Testing

TODO

## Error Handling 

TODO 


