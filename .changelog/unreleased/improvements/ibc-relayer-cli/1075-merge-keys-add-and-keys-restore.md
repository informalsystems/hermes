- Merged commands `keys add` and `keys restore` into single command `keys add`. Restoring a key now takes a
  file containing the mnemonic as input instead of directly taking the mnemonic
  as input. ([#1075](https://github.com/informalsystems/ibc-rs/issues/1075))