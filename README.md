# ibc-rs

[![Build Status][build-image]][build-link]
[![End to End testing][e2e-image]][e2e-link]
[![Apache 2.0 Licensed][license-image]][license-link]
![Rust Stable][rustc-image]
![Rust 1.53+][rustc-version]

Rust implementation of the Inter-Blockchain Communication (IBC) protocol.

This project comprises primarily four crates:

- The [`ibc`][ibc-crate-link] crate defines the main data structures and
  on-chain logic for the IBC protocol.
- The [`ibc-relayer`][relayer-crate-link] crate provides an implementation
  of an IBC relayer, as a _library_.
- The [`ibc-relayer-cli`][relayer-cli-crate-link] crate is a CLI (a wrapper
  over the `ibc-relayer` library), comprising the
  [`hermes`](https://hermes.informal.systems) binary.
- The [`ibc-proto`][ibc-proto-crate-link] crate is a library with Rust types generated from .proto definitions
  necessary for interacting with [Cosmos SDK](https://github.com/cosmos/cosmos-sdk/tree/master/proto/cosmos)
  and its [IBC structs](https://github.com/cosmos/ibc-go/tree/main/proto/ibc).
- The [`ibc-telemetry`][ibc-telemetry-crate-link] crate is a library for use in the `hermes` CLI,
  for gathering telemetry data and exposing that in a Prometheus endpoint.

See the table below for more details.

Includes [TLA+ specifications](/docs/spec).

| Crate name    |   Type   |     Version       | Docs   |
|:-------------:|:------:|:-------------:|:-----:|
| [ibc](./modules) (modules) | lib|  [![IBC Crate][ibc-crate-image]][ibc-crate-link] | [![IBC Docs][ibc-docs-image]][ibc-docs-link] |
| [ibc-relayer](./relayer)      | lib |  [![IBC Relayer Crate][relayer-crate-image]][relayer-crate-link]  | [![IBC Relayer Docs][relayer-docs-image]][relayer-docs-link] |
| [ibc-relayer-cli](./relayer-cli)  | bin: [hermes](relayer-cli/) |  [![IBC Relayer CLI Crate][relayer-cli-crate-image]][relayer-cli-crate-link]      |  [![IBC Relayer CLI Docs][relayer-cli-docs-image]][relayer-cli-docs-link] |
| [ibc-proto](./proto)  | lib |  [![IBC Proto Crate][ibc-proto-crate-image]][ibc-proto-crate-link]      |  [![IBC Proto Docs][ibc-proto-docs-image]][ibc-proto-docs-link] |
| [ibc-telemetry](./telemetry)  | lib |  [![IBC Telemetry Crate][ibc-telemetry-crate-image]][ibc-telemetry-crate-link]      |  [![IBC Telemetry Docs][ibc-telemetry-docs-image]][ibc-telemetry-docs-link] |


## Requirements

Developed with the latest stable version of Rust: `1.53.0`.
(May work with older versions.)

## Hermes Guide

The relayer CLI binary, called `hermes`, has a comprehensive guide at
[hermes.informal.systems](http://hermes.informal.systems).

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

Copyright © 2021 Informal Systems Inc. and ibc-rs authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

[ibc-crate-image]: https://img.shields.io/crates/v/ibc.svg
[ibc-crate-link]: https://crates.io/crates/ibc
[ibc-docs-image]: https://docs.rs/ibc/badge.svg
[ibc-docs-link]: https://docs.rs/ibc/
[relayer-crate-image]: https://img.shields.io/crates/v/ibc-relayer.svg
[relayer-crate-link]: https://crates.io/crates/ibc-relayer
[relayer-docs-image]: https://docs.rs/ibc-relayer/badge.svg
[relayer-docs-link]: https://docs.rs/ibc-relayer/
[relayer-cli-crate-image]: https://img.shields.io/crates/v/ibc-relayer-cli.svg
[relayer-cli-crate-link]: https://crates.io/crates/ibc-relayer-cli
[relayer-cli-docs-image]: https://docs.rs/ibc-relayer-cli/badge.svg
[relayer-cli-docs-link]: https://docs.rs/ibc-relayer-cli/
[ibc-proto-crate-image]: https://img.shields.io/crates/v/ibc-proto.svg
[ibc-proto-crate-link]: https://crates.io/crates/ibc-proto
[ibc-proto-docs-image]: https://docs.rs/ibc-proto/badge.svg
[ibc-proto-docs-link]: https://docs.rs/ibc-proto/
[ibc-telemetry-crate-image]: https://img.shields.io/crates/v/ibc-telemetry.svg
[ibc-telemetry-crate-link]: https://crates.io/crates/ibc-telemetry
[ibc-telemetry-docs-image]: https://docs.rs/ibc-telemetry/badge.svg
[ibc-telemetry-docs-link]: https://docs.rs/ibc-telemetry/

[build-image]: https://github.com/informalsystems/ibc-rs/workflows/Rust/badge.svg
[build-link]: https://github.com/informalsystems/ibc-rs/actions?query=workflow%3ARust
[e2e-image]: https://github.com/informalsystems/ibc-rs/workflows/End%20to%20End%20testing/badge.svg
[e2e-link]: https://github.com/informalsystems/ibc-rs/actions?query=workflow%3A%22End+to+End+testing%22
[license-image]: https://img.shields.io/badge/license-Apache_2.0-blue.svg
[license-link]: https://github.com/informalsystems/ibc-rs/blob/master/LICENSE
[rustc-image]: https://img.shields.io/badge/rustc-stable-blue.svg
[rustc-version]: https://img.shields.io/badge/rustc-1.53+-blue.svg
