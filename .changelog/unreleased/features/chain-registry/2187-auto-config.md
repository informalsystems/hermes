- New crate `chain-registry` to fetch data from the [chain-registry](https://github.com/cosmos/chain-registry/tree/master/cosmoshub) and generate `Vec<ChainConfig>` for Hermes.
  ([#2187](https://github.com/informalsystems/ibc-rs/issues/2187))

- `utils.rs` contains the default implementation of the trait `Fetchable` which fetches data from the chain-registry and deserialize it to a generic struct implementing Deserialize.
- `asset_list.rs` contains structs and definitions to serialize and deserialize data from `chain_name/assetlist.json` files.
- `chain.rs` contains structs and definitions to serialize and deserialize from `chain_name/chain.json` files.
- `path.rs` contains structs and definitions to serialize and deserialize from `_IBC/chain_1-chain_2.json` files
- `error.rs` contains the definition of every `RegistryError`.
- `relayer_config.rs` contains functions to generate `Vec<ChainConfig>`