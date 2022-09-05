# Hermes Guide ({{#template templates/version}})

## Overview 

Hermes is an open-source Rust implementation of a relayer for the
[Inter-Blockchain Communication protocol](https://ibc.cosmos.network) (**IBC**) released under the [ibc-relayer-cli](https://crates.io/crates/ibc-relayer-cli) crate. It provides a CLI to relay packets between Cosmos SDK chains, exposes [Prometheus](https://prometheus.io/) metrics and offers a REST API. 

This guide can help you set up, configure, operate and monitor Hermes to relay
packets between two or more IBC-enabled chains.

## About Hermes

An IBC relayer is an off-chain process responsible for relaying IBC datagrams between any two chains. The way it does so is by scanning chain states, building transactions based on these states, and submitting the transactions to the chains involved in the network.

The relayer is a central element in the IBC network architecture. This is because chain modules in this architecture are not directly sending messages to each other over networking infrastructure, but instead they create and store the data to be retrieved and used by a relayer to build the IBC datagrams.

We sometimes refer to Hermes as "IBC Relayer CLI", to make it clear that this is a relayer CLI (i.e., a binary) and distinguish it from the relayer core library (that is the crate called ibc-relayer).

Hermes is actively developed and maintained by [Informal Systems](https://informal.systems) in the [ibc-rs](https://github.com/informalsystems/ibc-rs) repository.

## Where to go

* **[Glossary](./glossary.md)**

  - This section provides some definitions of terms used throughout the guide.


* **[Quick start](./quick-start/index.md)**

  - This section can help you install Hermes.

* **[Tutorials](./tutorials/index.md)**

  - **[Prerequisites for local chains](./tutorials/local-chains/index.md)**
      - Install `Gaia` and `gm` (Gaia Manager) for tutorials using local chains.
  - **[Two Local Chains](./tutorials/local-chains/index.md)**
      - Start two local [`Cosmos Gaia`](https://github.com/cosmos/gaia) chains that support the `IBC` protocol and learn the fundamentals of IBC.
  - **[More Local Chains](./tutorials/more-chains/index.md)**
      - Learn how to relay on an arbitrary topology of more than two chains by using packet filters and to run multiple instances of Hermes.
  - **[Relaying in production](./tutorials/production/index.md)**
      - Learn how to set up, configure and run `hermes` on IBC-enabled chains in production.

* **[Advanced](./advanced/index.md)**
  - **[Features](./advanced/features.md)** 
      - This section summarizes Hermes' features and includes a comparison between the Cosmos Go relayer and Hermes.
  - **[Troubleshooting](./advanced/troubleshooting/index.md)**
      - Learn the general guidelines regarding troubleshooting.
    

* **[Documentation](./documentation/index.md)**
  - **[Configuration](./documentation/configuration/index.md)**
      - This section includes everything you need to know to configure Hermes.
  - **[Telemetry](./documentation/telemetry/index.md)**
      - This section describes all Prometheus metrics and how to use them efficiently.
  - **[REST API](./documentation/rest-api.md)**
      - This section presents Hermes' REST API.
  - **[Commands Reference](./documentation/commands/index.md)**
      - This section describes the command line interface from which you can interact with Hermes.

* Educational resources
  - [About IBC](https://ibc.cosmos.network/)
      - The official IBC-Go documentation. 
  - [Cosmos network tutorial](https://tutorials.cosmos.network/academy/4-ibc/what-is-ibc.html#)
      - Learn the basics of IBC in the official tutorial. 
  - [Connect IBC enabled chains with Hermes](https://www.youtube.com/watch?v=_xQDTj1PcEw&t=4289s)
      - Video demonstration of Hermes at Hackatom 2021.

* Useful links
  - [Hermes FAQ Page](https://github.com/informalsystems/ibc-rs/discussions/2472)
      - The official FAQ of Hermes.
  - [Hermes GitHub repository](https://github.com/informalsystems/ibc-rs)
      - The official GitHub repository for Hermes.
  - [IBC GitHub repository](https://github.com/cosmos/ics)
      - The official repository for the Inter-blockchain protocol (IBC).
  - [IBC Protocol](https://ibcprotocol.org)
      - The official IBC protocol page.

## Contact

- Request a [new feature](#new-feature-request) via the [feature request][feature-request] issue template;
- Consult the [list of reported issues][issues] and search by relevant
  keywords to see if you're dealing with a known problem;
- We would be grateful if you can submit a [bug report][bug-report]
  discussing any problem you find, and from there on we can look at the
  problem together;
- Reach Hermes developpers and other relayer operators on the [Cosmos Network Discord server](https://discord.com/invite/cosmosnetwork).

Lastly, for general questions, you can reach us at `hello@informal.systems`,
or on Twitter [@informalinc][twitter].

> Note that Hermes is packaged as part of the `ibc-relayer-cli` crate.


---

__Disclaimer__ This project is undergoing heavy development, use at your own risk.

---



[feature-request]: https://github.com/informalsystems/ibc-rs/issues/new?assignees=&labels=&template=feature-request.md
[bug-report]: https://github.com/informalsystems/ibc-rs/issues/new?assignees=&labels=&template=bug-report.md
[twitter]: https://twitter.com/informalinc
[issues]: https://github.com/informalsystems/ibc-rs/issues