*August 22nd, 2022*

After more than 2 years in the works, this is the first stable release of the Hermes relayer! 🎉

### Note for operators

> ⚠️  If upgrading from Hermes v0.15.0, be aware that this release contains multiple breaking
> ⚠️  changes to the Hermes command-line interface and configuration.
> ⚠️  Please consult the [UPGRADING document for instructions](UPGRADING.md) ) for a more detadetails.

### Highlights

- The performance and reliability of the relayer has been greatly improved
- Merged commands `keys add` and `keys restore` into single command `keys add`
  The flag to specify the key name for the CLI command `keys add` has been changed
  from `-n` to `-k`. Restoring a key now takes a file containing the mnemonic as
  input instead of directly taking the mnemonic
- Deprecated `gas_adjustment` setting in favor of new `gas_multiplier` setting
- Updated all CLI commands to take flags instead of positional arguments
- Renamed `query packet unreceived-packets` to `query packet pending-sends`
  and `query packet unreceived-acks` to `query packet pending-acks`
- Added CLI command `keys balance` which outputs the balance of an account associated with a key
- Added CLI command `query channel client` which outputs the channel's client state
- Added CLI command `query transfer denom-trace` which outputs the base denomination and path of a given trace hash
- Dropped the `raw` prefix from all the `tx raw` commands
- Remove the four duplicate commands:
  * `tx raw update-client`, which is the same as `update client`
  * `tx raw upgrade-client`, which is the same as `upgrade client`
  * `tx raw upgrade-clients`, which is the same as `upgrade clients`
  * `tx raw create-client`, which is the same as `create client`
- [A new section was added to guide][telemetry-guide] which describes how the new metrics
  can be used to observe both the current state of the relayer and the networks it is connected to
- Added many new metrics to the telemetry. The full list can be found in new the guide section linked above

### Change to the versioning scheme

As of v1.0.0-rc.0, the Hermes CLI is now versioned separately from
the other crates in the project. As such, the top-level version
designates the version of the Hermes CLI, but the other crates in
the repository do not necessarily match this version. For example,
the `ibc` and `ibc-relayer` crates are released under version 0.19.0
for Hermes v1.0.0.

The structure of this changelog has therefore changed as well,
changes are now grouped first by crate and then by the type of change,
eg. feature, bug fix, etc.

### Full release notes

The release notes below only contain the changes introduced since v1.0.0-rc.2.
For the full list of changes since v0.15.0, please consult the sections below for
v1.0.0-rc.2, v1.0.0-rc.1 and v1.0.0-rc.0.
