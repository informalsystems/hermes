- Add CosmWasm support to the generated Protobuf code ([#1913](https://github.com/informalsystems/ibc-rs/issues/1913))
  * Add a new `client` feature to gate the tonic client code, implies the `std` feature.
  * Add a new `json-schema` feature to derive `schemars::JsonSchema` on some proto types, implies the `std` feature.
  * Add `#[serde(default)]` to fields that might be omitted by Golang `omitempty` directive.
  * Change serialization of byte arrays to Base64 for compatibility with Go.
