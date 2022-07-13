- Merged commands `keys add` and `keys restore` into single command `keys add`.
  The flag to specify the key name for the CLI command `keys add` has been changed from `-n` to `-k`.
  Restoring a key now takes a file containing the mnemonic as input instead of directly taking the mnemonic.
  ([#1075](https://github.com/informalsystems/ibc-rs/issues/1075))
