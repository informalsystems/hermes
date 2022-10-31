*October 28th, 2022*

### Note to developers

The [`ibc`][ibc] and [`ibc-proto`][ibc-proto] crates
[have been split into their own repositories][split-tweet] under
the `cosmos` organization.

Moreover, Hermes [will not be using][split-issue] the original `ibc` crate anymore,
and will from now on use instead the `ibc-relayer-types` crate, which is a
trimmed down version of the `ibc` crate that contains only the data structures used by Hermes.

This change does not impact end-users of Hermes, but may affect downstream
consumers of the `ibc-relayer` library in some cases.

Please reach out to us if you encounter any issue following from
this reorganization of the repository.

[ibc]: https://github.com/cosmos/ibc-rs
[ibc-proto]: https://github.com/cosmos/ibc-proto-rs
[cosmos]: https://github.com/cosmos
[split-tweet]: https://twitter.com/informalinc/status/1578120684508692481
[split-issue]: https://github.com/informalsystems/hermes/issues/2639

