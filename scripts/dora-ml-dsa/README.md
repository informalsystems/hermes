# Dora ML-DSA-65 validator header experiment

The optional dependency overlay preserves the original Cosmos relayer key ring.
It adds the CometBFT 0.40 validator key JSON tag, the `ml_dsa_65` consensus
parameter, and protobuf oneof field 4,
checks the 1,952-byte public key and 3,309-byte signature, derives the validator
address from SHA-256, and verifies canonical votes via FIPS 204 with an empty
context. The original light-client trust rules are retained.

Run `prepare-deps.sh /path/to/scratch` and build from an isolated checkout
containing the CometBFT 0.40 RPC compatibility change:

```sh
cargo --config /path/to/scratch/rust-patches.toml \
  build -p ibc-relayer-cli --bin hermes
```

Cargo updates the lockfile in that checkout to record the two patched crates
and the pinned FIPS 204 library. Subsequent builds can use `--locked`.
The overlay does not introduce an ML-DSA transaction signer.

To check a Go reference fixture, place `probe-header.rs` at
`crates/relayer/examples/probe-dora-header.rs` in the isolated checkout:

```sh
cargo --config /path/to/scratch/rust-patches.toml \
  run -p ibc-relayer --example probe-dora-header -- /path/to/fixture.json
```
