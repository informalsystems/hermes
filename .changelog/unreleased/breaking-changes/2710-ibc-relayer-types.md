After the [`ibc`][ibc] and [`ibc-proto`][ibc-proto] crates
[were split into their own repositories][split-tweet] under
the `cosmos` organization, we were left with a copy of
the `ibc` crate in the `modules` directory.

Hermes [will not be using][split-issue] the original `ibc` crate anymore,
so we decided to rename the leftover copy of the `ibc` crate to `ibc-relayer-types`,
and to trim it down to contain only the data structures used by the relayer.

This change does not impact end-users of Hermes, but may affect downstream
consumers of the `ibc-relayer` library in some cases.

Please reach out to us if you encounter any issue following from
this reorganization of the repository.

[ibc]: https://github.com/cosmos/ibc-rs
[ibc-proto]: https://github.com/cosmos/ibc-proto-rs
[cosmos]: https://github.com/cosmos
[split-tweet]: https://twitter.com/informalinc/status/1578120684508692481
[split-issue]: https://github.com/informalsystems/hermes/issues/2639
