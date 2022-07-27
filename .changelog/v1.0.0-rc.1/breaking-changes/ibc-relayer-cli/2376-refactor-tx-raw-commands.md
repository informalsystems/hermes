- Refactored old `tx raw` commands to drop the `raw` subcommand.
  Replaced `--src-` and `--dst-` flag prefixes in old `tx raw` commands with more meaningful prefixes.
  Removed commands `tx raw update-client`, `tx raw upgrade-client`, `tx raw upgrade-client` and
  `tx raw create-client`.
  ([#2376](https://github.com/informalsystems/ibc-rs/issues/2376))