# Gaiad Manager Change Log

## v0.1.3

### BUGFIXES

- Fixed variable TM to reference the GAIAD_BINARY ([#2210]).

[#2210]: https://github.com/informalsystems/ibc-rs/issues/2210

## v0.1.2

### BUGFIXES

- Fixed `gm hermes keys` which was broken following a breaking change in Hermes CLI ([#2262]).

### IMPROVEMENTS

- Adjusted the `max_gas` and `gas_price.price` parameters used for `gm hermes config`.

[#2262]: https://github.com/informalsystems/ibc-rs/issues/2262


## v0.1.1

### BUGFIXES

- Added `unsafe-reset-all` support for SDK 0.44.8+ and 0.45.3+ ([#2162])


[#2162]: https://github.com/informalsystems/ibc-rs/issues/2162

## v0.1.0

### FEATURES
- Implemented JSON output if `OUTPUT=json` is set in the environment.
- Added the `extra_wallets` parameter to generate extra wallets for networks.

### BUGFIXES
- Increased default Hermes config constants `rpc_timeout` and `max_gas`.
- Fixed default for `$OUPUT` in `lib-gm`.
- Updated Hermes config for Hermes 0.9.0 compatibility.

## v0.0.9

### FEATURES
- Binaries in the config can be defined as URLs now.
- Add the option to set gm-lib path via the $GM_LIB environment variable ([#1365])

### BUGFIXES
- Fixed debug messages not printing to stdout properly.
- Minor cosmetic fixes.

## v0.0.8

### BUGFIXES
- Fixed gaiad 0.43 keys add printing key to stderr instead of stdout issue ([#1312])
- Bumped default rpc_timeout in Hermes config to 5s ([#1312])

[#1312]: https://github.com/informalsystems/ibc-rs/issues/1312
[#1365]: https://github.com/informalsystems/ibc-rs/issues/1365

## v0.0.7

### BUGFIXES
- Fixed gm not reporting missing dependencies ([#1261])

[#1261]: https://github.com/informalsystems/ibc-rs/issues/1261

## v0.0.6

### FEATURES
- Compatibility of hermes updated to 0.4.1 and above. ([#1049])
- Enabled swagger page on the gaiad APP port.

### BUGFIXES
- Re-enable APP port in configuration ([comment](https://github.com/informalsystems/ibc-rs/pull/1051#issuecomment-856024919))

[#1049]: https://github.com/informalsystems/ibc-rs/issues/1049

## v0.0.5 (unreleased)

### FEATURES
- Reorganized the documentation and moved the configuration file documentation into the example configuration.
- Added auto-configuration of the `denom` and `prefix` options in hermes config.

### BUGFIXES
- Fixed a small bug with the DEBUG features (used `==` instead of `=` when testing for the `DEBUG` flag.)
- Fixed the 5-network mesh example configuration in the documentation.
- Removed `--x-crisis-skip-assert-invariants` as not all networks support it.
- Only add node to the hermes config if there is no node already for that network

### REFACTORS
- Reorganized the `lib-gm` file to make it slightly easier to add configuration options.
- Simplified the empty "default" config that gets created if no config exists.
- Moved away from the `testnet` command as not all networks support it.
- Renamed `wallet_hdpath` configuration item to `hdpath` to reflect that the validator address is also impacted during
  creation.

## v0.0.4

### FEATURES
- Updated hermes configuration with the hermes 0.4.0 configuration parameters.

## v0.0.3

### BUGFIXES
- Apply defaults to missing configuration options ([#993])

### FEATURES
- Separated hermes configuration into the `global.hermes` section in the configuration

### Dependencies
- Requires stoml 0.7.0 or above

[#993]: https://github.com/informalsystems/ibc-rs/issues/993

## v0.0.2

### BUGFIXES
- Import hermes keys properly even if hdpath is set ([#975])

### FEATURES
- Introduced [CHANGELOG](https://github.com/informalsystems/ibc-rs/blob/master/scripts/gm/CHANGELOG.md) file.

[#975]: https://github.com/informalsystems/ibc-rs/issues/975

## v0.0.1

### FEATURES
- Initial release ([#902])

[#902]: https://github.com/informalsystems/ibc-rs/issues/902
