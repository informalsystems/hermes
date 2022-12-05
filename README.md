# ibc-rs

[![Cosmos ecosystem][cosmos-shield]][cosmos-link]

[![Build Status][build-image]][build-link]
[![End to End testing][e2e-image]][e2e-link]
[![Apache 2.0 Licensed][license-image]][license-link]
![Rust Stable][rustc-image]
![Rust 1.65+][rustc-version]

Rust implementation of an Inter-Blockchain Communication (IBC) relayer.

This project comprises primarily of 5 crates:

- [`ibc-relayer`][relayer-crate-link] provides an implementation of an IBC relayer, as a _library_.
- [`ibc-relayer-cli`][relayer-cli-crate-link] is a CLI (a wrapper over the `ibc-relayer` library),
  comprising the [`hermes`](https://hermes.informal.systems) binary.
- [`ibc-chain-registry`][ibc-chain-registry-crate-link] provides functions to fetch data from
  the [chain registry](https://github.com/cosmos/chain-registry) and automatically generate chain
  configuration for Hermes.
- [`ibc-telemetry`][ibc-telemetry-crate-link] is a library for use in the Hermes CLI,
  for gathering telemetry data and exposing that in a Prometheus endpoint.
- [`ibc-relayer-rest`][ibc-telemetry-crate-link] is a library for use in the Hermes CLI,
  for exposing a REST API to inspect the state of the relayer.
- [`ibc-test-framework`][ibc-test-framework-crate-link] provides the infrastructure and framework
  for writing end-to-end (E2E) tests that include the spawning of the relayer together with Cosmos full nodes.


See the table below for more details.

> ⚠️  The [`ibc`][ibc-rs-repo] and [`ibc-proto`][ibc-proto-rs-repo] crates have been moved to their own repositories.

The repository also includes [TLA+ specifications](docs/spec).

## Status

| Crate name                                   |   Type                     |     Version                                                                                  | Docs   |
|:-------------:|:------:|:-------------:|:-----:|
| [ibc-relayer-cli](crates/relayer-cli)             | bin: [hermes](crates/relayer-cli/) | [![IBC Relayer CLI Crate][relayer-cli-crate-image]][relayer-cli-crate-link]                  | [![IBC Relayer CLI Docs][relayer-cli-docs-image]][relayer-cli-docs-link]                  |
| [ibc-relayer](crates/relayer)                     | lib                         | [![IBC Relayer Crate][relayer-crate-image]][relayer-crate-link]                              | [![IBC Relayer Docs][relayer-docs-image]][relayer-docs-link]                              |
| [ibc-chain-registry](crates/ibc-chain-registry)                             | lib                         | [![Chain Registry Crate][ibc-chain-registry-crate-image]][ibc-chain-registry-crate-link]                                              | [![Chain Registry Docs][ibc-chain-registry-docs-image]][ibc-chain-registry-docs-link]                                              |
| [ibc-relayer-rest](crates/relayer-rest)           | lib                         | [![IBC Relayer REST Crate][relayer-rest-crate-image]][relayer-rest-crate-link]               | [![IBC Relayer REST Docs][relayer-rest-docs-image]][relayer-rest-docs-link]               |
| [ibc-telemetry](crates/telemetry)                 | lib                         | [![IBC Telemetry Crate][ibc-telemetry-crate-image]][ibc-telemetry-crate-link]                | [![IBC Telemetry Docs][ibc-telemetry-docs-image]][ibc-telemetry-docs-link]                |
| [ibc-test-framework](./tools/test-framework) | lib                         | [![IBC Test Framework Crate][ibc-test-framework-crate-image]][ibc-test-framework-crate-link] | [![IBC Test Framework Docs][ibc-test-framework-docs-image]][ibc-test-framework-docs-link] |


## Requirements

The crates in this project require Rust `1.65.0`.

## Hermes Guide

We have a comprehensive guide at [hermes.informal.systems](http://hermes.informal.systems).

## Contributing

IBC is specified in English in the [cosmos/ibc repo](https://github.com/cosmos/ibc). Any
protocol changes or clarifications should be contributed there.

This repo contains the TLA+ specification and Rust implementation for the IBC
modules and relayer. If you're interested in contributing, please comment on an issue or open a new one!

See also [CONTRIBUTING.md](./CONTRIBUTING.md).

## Versioning

We follow [Semantic Versioning](https://semver.org/), though APIs are still
under active development.

## Resources

- [IBC Website](https://cosmos.network/ibc)
- [IBC Specification](https://github.com/cosmos/ibc)
- [IBC Modules in Go](https://github.com/cosmos/ibc-go)
- [IBC Relayer in Typescript](https://github.com/confio/ts-relayer)
- [IBC Relayer in Go](https://github.com/cosmos/relayer)

## License

Copyright © 2022 Informal Systems Inc. and ibc-rs authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.


