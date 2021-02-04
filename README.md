# ibc-rs

[![Build Status][build-image]][build-link]
[![End to End testing][e2e-image]][e2e-link]
[![Apache 2.0 Licensed][license-image]][license-link]
![Rust Stable][rustc-image]
![Rust 1.49+][rustc-version]

Rust implementation of the Inter-Blockchain Communication (IBC) protocol.

This project consists of the following crates:
 
 - The [`ibc`](https://docs.rs/ibc) crate defines the main data structures and on-chain logic  for the IBC protocol.
- The [`ibc-relayer`](https://docs.rs/ibc-relayer) crate provides an implementation of an IBC relayer, as a library.
- [`hermes`](https://hermes.informal.systems) is a command-line interface for the IBC relayer provided by this project.

See the table below for details.

Includes [TLA+ specifications](/docs/spec).

> TODO: update the crate and docs links below (for relayer and relayer-cli).

| Crate name    |   Type   |     Version       | Docs   |
|:-------------:|:------:|:-------------:|:-----:|
| [ibc (modules)](./modules) | lib|  [![IBC Crate][ibc-crate-image]][ibc-crate-link] | [![Docs][ibc-docs-image]][ibc-docs-link] |
| [ibc-relayer](./relayer)      | lib |  [![Relayer Crate][relayer-crate-image]][relayer-crate-link]  | [![Docs][relayer-docs-image]][relayer-docs-link] |
| [ibc-relayer-cli](./relayer-cli)  | bin: [hermes](relayer-cli/) |  [![Relayer CLI Crate][relayer-cli-crate-image]][relayer-cli-crate-link]      |  [![Docs][relayer-cli-docs-image]][relayer-cli-docs-link] |


## Requirements 

Developed with the latest stable version of Rust: `1.49.0`. 
(May work with older versions.)

## Relayer guide

The main relayer CLI binary, called `hermes`, has a comprehensive guide at
[hermes.informal.systems](http://hermes.informal.systems).

## Contributing

IBC is specified in English in the [cosmos/ics repo](https://github.com/cosmos/ics). Any
protocol changes or clarifications should be contributed there.

This repo contains the TLA+ specification and Rust implementation for the IBC
modules and relayer. If you're interested in contributing, please comment on an issue or open a new
one!

See also [CONTRIBUTING.MD](./CONTRIBUTING.md).

## Versioning

We follow [Semantic Versioning](https://semver.org/), though APIs are still 
under active development.

## Resources

- [IBC Website](https://cosmos.network/ibc)
- [IBC Specification](https://github.com/cosmos/ics)
- [IBC Modules in Go](https://github.com/cosmos/cosmos-sdk/tree/master/x/ibc)
- [IBC Relayer in Go](https://github.com/iqlusioninc/relayer)

## License

Copyright © 2021 Informal Systems Inc. and ibc-rs authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

[ibc-crate-image]: https://img.shields.io/crates/v/ibc.svg
[ibc-crate-link]: https://crates.io/crates/ibc
[ibc-docs-image]: https://docs.rs/ibc/badge.svg
[ibc-docs-link]: https://docs.rs/ibc/
[relayer-crate-image]: https://img.shields.io/crates/v/ibc.svg
[relayer-crate-link]: https://crates.io/crates/ibc
[relayer-docs-image]: https://docs.rs/ibc/badge.svg
[relayer-docs-link]: https://docs.rs/ibc/
[relayer-cli-crate-image]: https://img.shields.io/crates/v/ibc.svg
[relayer-cli-crate-link]: https://crates.io/crates/ibc
[relayer-cli-docs-image]: https://docs.rs/ibc/badge.svg
[relayer-cli-docs-link]: https://docs.rs/ibc/

[build-image]: https://github.com/informalsystems/ibc-rs/workflows/Rust/badge.svg
[build-link]: https://github.com/informalsystems/ibc-rs/actions?query=workflow%3ARust
[e2e-image]: https://github.com/informalsystems/ibc-rs/workflows/End%20to%20End%20testing/badge.svg
[e2e-link]: https://github.com/informalsystems/ibc-rs/actions?query=workflow%3A%22End+to+End+testing%22
[license-image]: https://img.shields.io/badge/license-Apache_2.0-blue.svg
[license-link]: https://github.com/informalsystems/ibc-rs/blob/master/LICENSE
[rustc-image]: https://img.shields.io/badge/rustc-stable-blue.svg
[rustc-version]: https://img.shields.io/badge/rustc-1.49+-blue.svg
