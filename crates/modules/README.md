# IBC module

[![Crate][crate-image]][crate-link]
[![Docs][docs-image]][docs-link]
[![Build Status][build-image]][build-link]
[![End to End testing][e2e-image]][e2e-link]
[![Apache 2.0 Licensed][license-image]][license-link]
![Rust Stable][rustc-image]
![Rust 1.51+][rustc-version]


See the [ibc-rs] repo root for more detailed information on how this crate can be used.


Implementation of the Inter-Blockchain Communication Protocol ([IBC]) module.

## Documentation

See documentation on [docs.rs][docs-link].

## Divergence from the Interchain Standards (ICS)
This crate diverges from the [ICS specification](https://github.com/cosmos/ibc) in a number of ways. See below for more details.

### Module system: no support for untrusted modules
ICS 24 (Host Requirements) gives the [following requirement](https://github.com/cosmos/ibc/blob/master/spec/core/ics-024-host-requirements/README.md#module-system) about the module system that the host state machine must support:

> The host state machine must support a module system, whereby self-contained, potentially mutually distrusted packages of code can safely execute on the same ledger [...].

**This crate currently does not support mutually distrusted packages**. That is, modules on the host state machine are assumed to be fully trusted. In practice, this means that every module has either been written by the host state machine developers, or fully vetted by them.

### Port system: No object capability system
ICS 5 (Port Allocation) requires the host system to support either object-capability reference or source authentication for modules.

> In the former object-capability case, the IBC handler must have the ability to generate object-capabilities, unique, opaque references which can be passed to a module and will not be duplicable by other modules. [...]
> In the latter source authentication case, the IBC handler must have the ability to securely read the source identifier of the calling module, a unique string for each module in the host state machine, which cannot be altered by the module or faked by another module.

**This crate currently requires neither of the host system**. Since modules are assumed to be trusted, there is no need for this object capability system that protects resources for potentially malicious modules.

For more background on this, see [this issue](https://github.com/informalsystems/ibc-rs/issues/2159).

### Port system: transferring and releasing a port
ICS 5 (Port Allocation) requires the IBC handler to permit [transferring ownership of a port](https://github.com/cosmos/ibc/tree/master/spec/core/ics-005-port-allocation#transferring-ownership-of-a-port) and [releasing a port](https://github.com/cosmos/ibc/tree/master/spec/core/ics-005-port-allocation#releasing-a-port).

We currently support neither.

## License

Copyright © 2021 Informal Systems Inc. and ibc-rs authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

[//]: # (badges)

[crate-image]: https://img.shields.io/crates/v/ibc.svg
[crate-link]: https://crates.io/crates/ibc
[docs-image]: https://docs.rs/ibc/badge.svg
[docs-link]: https://docs.rs/ibc/

[build-image]: https://github.com/informalsystems/ibc-rs/workflows/Rust/badge.svg
[build-link]: https://github.com/informalsystems/ibc-rs/actions?query=workflow%3ARust
[e2e-image]: https://github.com/informalsystems/ibc-rs/workflows/End%20to%20End%20testing/badge.svg
[e2e-link]: https://github.com/informalsystems/ibc-rs/actions?query=workflow%3A%22End+to+End+testing%22

[license-image]: https://img.shields.io/badge/license-Apache2.0-blue.svg
[license-link]: https://github.com/informalsystems/ibc-rs/blob/master/LICENSE
[rustc-image]: https://img.shields.io/badge/rustc-stable-blue.svg
[rustc-version]: https://img.shields.io/badge/rustc-1.51+-blue.svg

[//]: # (general links)

[ibc-rs]: https://github.com/informalsystems/ibc-rs
[IBC]: https://github.com/cosmos/ibc
