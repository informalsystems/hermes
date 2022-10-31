- New crate `ibc-chain-registry` to fetch data from the [chain-registry](https://github.com/cosmos/chain-registry/tree/master/cosmoshub) and query RPC/gRPC endpoints.
  ([#2187](https://github.com/informalsystems/ibc-rs/issues/2187))

- `fetchable.rs` contains the default implementation of the trait `Fetchable` which fetches data from the chain-registry and deserialize it to a generic struct implementing Deserialize.
- `asset_list.rs` contains structs and definitions to serialize and deserialize data from `chain_name/assetlist.json` files.
- `chain.rs` contains structs and definitions to serialize and deserialize from `chain_name/chain.json` files.
- `path.rs` contains structs and definitions to serialize and deserialize from `_IBC/chain_1-chain_2.json` files
- `error.rs` contains the definition of every `RegistryError`.
- `constants.rs` contains chain names used for tests and the commit reference from which data is fetched.
- `formatter.rs` contains traits and struct to convert a string URL to a valid tendermint URL.
- `querier` contains traits and struct to query RPC / gRPC nodes.