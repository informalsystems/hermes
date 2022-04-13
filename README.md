# ibc-rs

[![Cosmos ecosystem][cosmos-shield]][cosmos-link]

[![Build Status][build-image]][build-link]
[![End to End testing][e2e-image]][e2e-link]
[![Apache 2.0 Licensed][license-image]][license-link]
![Rust Stable][rustc-image]
![Rust 1.60+][rustc-version]

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

Includes [TLA+ specifications](docs/spec).

| Crate name    |   Type   |     Version       | Docs   |
|:-------------:|:------:|:-------------:|:-----:|
| [ibc](./modules) (modules) | lib|  [![IBC Crate][ibc-crate-image]][ibc-crate-link] | [![IBC Docs][ibc-docs-image]][ibc-docs-link] |
| [ibc-relayer](./relayer)      | lib |  [![IBC Relayer Crate][relayer-crate-image]][relayer-crate-link]  | [![IBC Relayer Docs][relayer-docs-image]][relayer-docs-link] |
| [ibc-relayer-cli](./relayer-cli)  | bin: [hermes](relayer-cli/) |  [![IBC Relayer CLI Crate][relayer-cli-crate-image]][relayer-cli-crate-link]      |  [![IBC Relayer CLI Docs][relayer-cli-docs-image]][relayer-cli-docs-link] |
| [ibc-relayer-rest](./relayer-rest)  | lib |  [![IBC Relayer REST Crate][relayer-rest-crate-image]][relayer-rest-crate-link]      |  [![IBC Relayer REST Docs][relayer-rest-docs-image]][relayer-rest-docs-link] |
| [ibc-proto](./proto)  | lib |  [![IBC Proto Crate][ibc-proto-crate-image]][ibc-proto-crate-link]      |  [![IBC Proto Docs][ibc-proto-docs-image]][ibc-proto-docs-link] |
| [ibc-telemetry](./telemetry)  | lib |  [![IBC Telemetry Crate][ibc-telemetry-crate-image]][ibc-telemetry-crate-link]      |  [![IBC Telemetry Docs][ibc-telemetry-docs-image]][ibc-telemetry-docs-link] |


## Requirements

The crates in this project require the latest stable version of Rust: `1.60.0`.

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
[relayer-rest-crate-image]: https://img.shields.io/crates/v/ibc-relayer-rest.svg
[relayer-rest-crate-link]: https://crates.io/crates/ibc-relayer-rest
[relayer-rest-docs-image]: https://docs.rs/ibc-relayer-rest/badge.svg
[relayer-rest-docs-link]: https://docs.rs/ibc-relayer-rest/
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
[rustc-version]: https://img.shields.io/badge/rustc-1.60+-blue.svg
[cosmos-shield]: https://img.shields.io/static/v1?label=&labelColor=1B1E36&color=1B1E36&message=cosmos%20ecosystem&style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0idXRmLTgiPz4KPCEtLSBHZW5lcmF0b3I6IEFkb2JlIElsbHVzdHJhdG9yIDI0LjMuMCwgU1ZHIEV4cG9ydCBQbHVnLUluIC4gU1ZHIFZlcnNpb246IDYuMDAgQnVpbGQgMCkgIC0tPgo8c3ZnIHZlcnNpb249IjEuMSIgaWQ9IkxheWVyXzEiIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgeG1sbnM6eGxpbms9Imh0dHA6Ly93d3cudzMub3JnLzE5OTkveGxpbmsiIHg9IjBweCIgeT0iMHB4IgoJIHZpZXdCb3g9IjAgMCAyNTAwIDI1MDAiIHN0eWxlPSJlbmFibGUtYmFja2dyb3VuZDpuZXcgMCAwIDI1MDAgMjUwMDsiIHhtbDpzcGFjZT0icHJlc2VydmUiPgo8c3R5bGUgdHlwZT0idGV4dC9jc3MiPgoJLnN0MHtmaWxsOiM2RjczOTA7fQoJLnN0MXtmaWxsOiNCN0I5Qzg7fQo8L3N0eWxlPgo8cGF0aCBjbGFzcz0ic3QwIiBkPSJNMTI1Mi42LDE1OS41Yy0xMzQuOSwwLTI0NC4zLDQ4OS40LTI0NC4zLDEwOTMuMXMxMDkuNCwxMDkzLjEsMjQ0LjMsMTA5My4xczI0NC4zLTQ4OS40LDI0NC4zLTEwOTMuMQoJUzEzODcuNSwxNTkuNSwxMjUyLjYsMTU5LjV6IE0xMjY5LjQsMjI4NGMtMTUuNCwyMC42LTMwLjksNS4xLTMwLjksNS4xYy02Mi4xLTcyLTkzLjItMjA1LjgtOTMuMi0yMDUuOAoJYy0xMDguNy0zNDkuOC04Mi44LTExMDAuOC04Mi44LTExMDAuOGM1MS4xLTU5Ni4yLDE0NC03MzcuMSwxNzUuNi03NjguNGM2LjctNi42LDE3LjEtNy40LDI0LjctMmM0NS45LDMyLjUsODQuNCwxNjguNSw4NC40LDE2OC41CgljMTEzLjYsNDIxLjgsMTAzLjMsODE3LjksMTAzLjMsODE3LjljMTAuMywzNDQuNy01Ni45LDczMC41LTU2LjksNzMwLjVDMTM0MS45LDIyMjIuMiwxMjY5LjQsMjI4NCwxMjY5LjQsMjI4NHoiLz4KPHBhdGggY2xhc3M9InN0MCIgZD0iTTIyMDAuNyw3MDguNmMtNjcuMi0xMTcuMS01NDYuMSwzMS42LTEwNzAsMzMycy04OTMuNSw2MzguOS04MjYuMyw3NTUuOXM1NDYuMS0zMS42LDEwNzAtMzMyCglTMjI2Ny44LDgyNS42LDIyMDAuNyw3MDguNkwyMjAwLjcsNzA4LjZ6IE0zNjYuNCwxNzgwLjRjLTI1LjctMy4yLTE5LjktMjQuNC0xOS45LTI0LjRjMzEuNi04OS43LDEzMi0xODMuMiwxMzItMTgzLjIKCWMyNDkuNC0yNjguNCw5MTMuOC02MTkuNyw5MTMuOC02MTkuN2M1NDIuNS0yNTIuNCw3MTEuMS0yNDEuOCw3NTMuOC0yMzBjOS4xLDIuNSwxNSwxMS4yLDE0LDIwLjZjLTUuMSw1Ni0xMDQuMiwxNTctMTA0LjIsMTU3CgljLTMwOS4xLDMwOC42LTY1Ny44LDQ5Ni44LTY1Ny44LDQ5Ni44Yy0yOTMuOCwxODAuNS02NjEuOSwzMTQuMS02NjEuOSwzMTQuMUM0NTYsMTgxMi42LDM2Ni40LDE3ODAuNCwzNjYuNCwxNzgwLjRMMzY2LjQsMTc4MC40CglMMzY2LjQsMTc4MC40eiIvPgo8cGF0aCBjbGFzcz0ic3QwIiBkPSJNMjE5OC40LDE4MDAuNGM2Ny43LTExNi44LTMwMC45LTQ1Ni44LTgyMy03NTkuNVMzNzQuNCw1ODcuOCwzMDYuOCw3MDQuN3MzMDAuOSw0NTYuOCw4MjMuMyw3NTkuNQoJUzIxMzAuNywxOTE3LjQsMjE5OC40LDE4MDAuNHogTTM1MS42LDc0OS44Yy0xMC0yMy43LDExLjEtMjkuNCwxMS4xLTI5LjRjOTMuNS0xNy42LDIyNC43LDIyLjYsMjI0LjcsMjIuNgoJYzM1Ny4yLDgxLjMsOTk0LDQ4MC4yLDk5NCw0ODAuMmM0OTAuMywzNDMuMSw1NjUuNSw0OTQuMiw1NzYuOCw1MzcuMWMyLjQsOS4xLTIuMiwxOC42LTEwLjcsMjIuNGMtNTEuMSwyMy40LTE4OC4xLTExLjUtMTg4LjEtMTEuNQoJYy00MjIuMS0xMTMuMi03NTkuNi0zMjAuNS03NTkuNi0zMjAuNWMtMzAzLjMtMTYzLjYtNjAzLjItNDE1LjMtNjAzLjItNDE1LjNjLTIyNy45LTE5MS45LTI0NS0yODUuNC0yNDUtMjg1LjRMMzUxLjYsNzQ5Ljh6Ii8+CjxjaXJjbGUgY2xhc3M9InN0MSIgY3g9IjEyNTAiIGN5PSIxMjUwIiByPSIxMjguNiIvPgo8ZWxsaXBzZSBjbGFzcz0ic3QxIiBjeD0iMTc3Ny4zIiBjeT0iNzU2LjIiIHJ4PSI3NC42IiByeT0iNzcuMiIvPgo8ZWxsaXBzZSBjbGFzcz0ic3QxIiBjeD0iNTUzIiBjeT0iMTAxOC41IiByeD0iNzQuNiIgcnk9Ijc3LjIiLz4KPGVsbGlwc2UgY2xhc3M9InN0MSIgY3g9IjEwOTguMiIgY3k9IjE5NjUiIHJ4PSI3NC42IiByeT0iNzcuMiIvPgo8L3N2Zz4K
[cosmos-link]: https://cosmos.network
