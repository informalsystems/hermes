# Hermes Guide (v1.0.0)

## Overview 

Hermes is an open-source Rust implementation of a relayer for the
[Inter-Blockchain Communication protocol](https://ibc.cosmos.network) (**IBC**) released under the [ibc-relayer-cli](https://crates.io/crates/ibc-relayer-cli) crate. It provides a CLI to relay packets between Cosmos SDK chains, exposes [Prometheus](https://prometheus.io/) metrics and offers a REST API. 

This guide can help you setup, configure, operate and monitor Hermes to relay
packets between two or more IBC-enabled chains.

## About Hermes

An IBC relayer is an off-chain process responsible for relaying IBC datagrams between any two chains. The way it does so is by scanning chain states, building transactions based on these states, and submitting the transactions to the chains involved in the network.

The relayer is a central element in the IBC network architecture. This is because chain modules in this architecture are not directly sending messages to each other over networking infrastructure, but instead they create and store the data to be retrieved and used by a relayer to build the IBC datagrams.

We sometimes refer to Hermes as "IBC Relayer CLI", to make it clear that this is a relayer CLI (i.e., a binary) and distinguish it from the relayer core library (that is the crate called ibc-relayer).

Hermes is actively developed and maintained by [Informal Systems](https://informal.systems) in the [ibc-rs](https://github.com/informalsystems/ibc-rs) repository.

## Where to go

* **[Glossary](./glossary.md)**

  - This section provides some definitions of terms used throughout the guide.


* **[Quick start](./quick_start/index.md)**

  - This section can help you install Hermes.

* **[Tutorials](./tutorials/index.md)**

  - **Two local chains** TODO
  - **More local chains** TODO
  - **Relay in production** TODO
  - **Deploy multiple instances** TODO

* Advanced
  - **[Features](./features.md)** : This section discusses what features to expect from Hermes, as well as a comparison between the Cosmos Go relayer and Hermes.
  - **Troubleshooting**

* Documentation
  - **[Configuration](./config.md)**: How to configure Hermes.
  - **[Telemetry](./telemetry.md)**: Description of the Prometheus metrics.
  - **[REST API](./rest-api.md)**: Description of the REST API
  - **[Commands Reference](./commands/index.md)**: The commands let you interact with Hermes using its command line interface.

* Educational resources
  - [About IBC](https://ibc.cosmos.network/): TODO 
  - [Cosmos network tutorial](https://tutorials.cosmos.network/academy/4-ibc/what-is-ibc.html#): TODO 
  - Video : [Connect IBC enabled chains with Hermes](https://www.youtube.com/watch?v=_xQDTj1PcEw&t=4289s): TODO 

* Useful links
  - [Hermes Github repository](https://github.com/informalsystems/ibc-rs): The official Github repository for Hermes.
  - [IBC Github repository](https://github.com/cosmos/ics) : The official repository for the Inter-blockchain protocol (IBC).
  - [IBC Protocol](https://ibcprotocol.org) : The official IBC protocol page. (TODO : check description)

* Other

  - **[Help](./help.md)** : This part provides general resources for getting help.

---

__Disclaimer__ This project is undergoing heavy development, use at your own risk.

---

[^ibc]: [The Interblockchain Communication Protocol: An Overview](https://arxiv.org/pdf/2006.15918.pdf)
