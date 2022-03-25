use eyre::Report as Error;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::handle::CountingAndCachingChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::error::ErrorDetail as RelayerErrorDetail;
use ibc_relayer::keyring::errors::ErrorDetail as KeyringErrorDetail;
use ibc_relayer::registry::SharedRegistry;
use std::fs;
use std::path::Path;
use tracing::info;

use crate::types::single::node::FullNode;
use crate::types::wallet::{TestWallets, Wallet};

/**
   Create a new [`SharedRegistry`] that uses [`CountingAndCachingChainHandle`]
   as the [`ChainHandle`] implementation.
*/
pub fn new_registry(config: SharedConfig) -> SharedRegistry<CountingAndCachingChainHandle> {
    <SharedRegistry<CountingAndCachingChainHandle>>::new(config)
}

/**
   Spawn a new chain handle using the given [`SharedRegistry`] and
   [`FullNode`].

   The function accepts a proxy type `Seed` that should be unique
   accross multiple calls so that the returned [`ChainHandle`]
   have a unique type.

   For example, the following test should fail to compile:

   ```rust,compile_fail
   # use ibc_test_framework::bootstrap::binary::chain::spawn_chain_handle;
   fn same<T>(_: T, _: T) {}

   let chain_a = spawn_chain_handle(|| {}, todo!(), todo!()).unwrap();
   let chain_b = spawn_chain_handle(|| {}, todo!(), todo!()).unwrap();
   same(chain_a, chain_b); // error: chain_a and chain_b have different types
   ```

   The reason is that Rust would give each closure expression `||{}` a
   [unique anonymous type](https://doc.rust-lang.org/reference/types/closure.html).
   When we instantiate two chains with different closure types,
   the resulting values would be considered by Rust to have different types.

   With this we can treat `chain_a` and `chain_b` having different types
   so that we do not accidentally mix them up later in the code.
*/
pub fn spawn_chain_handle<Seed>(
    _: Seed,
    registry: &SharedRegistry<impl ChainHandle>,
    node: &FullNode,
) -> Result<impl ChainHandle, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry.get_or_spawn(chain_id)?;

    add_keys_to_chain_handle(&handle, &node.wallets)?;

    Ok(handle)
}

/**
   Add a wallet key to a [`ChainHandle`]'s key store.

   Note that if the [`ChainConfig`](ibc_relayer::config::ChainConfig) is
   configured to use in-memory store only, the added key would not be
   accessible through external CLI.
*/
pub fn add_key_to_chain_handle<Chain: ChainHandle>(
    chain: &Chain,
    wallet: &Wallet,
) -> Result<(), Error> {
    let res = chain.add_key(wallet.id.0.clone(), wallet.key.clone());

    // Ignore error if chain handle already have the given key
    match res {
        Err(e) => match e.detail() {
            RelayerErrorDetail::KeyBase(e2) => match e2.source {
                KeyringErrorDetail::KeyAlreadyExist(_) => Ok(()),
                _ => Err(e.into()),
            },
            _ => Err(e.into()),
        },
        Ok(()) => Ok(()),
    }
}

/**
   Add multiple wallets provided in [`TestWallets`] into the
   [`ChainHandle`]'s key store.
*/
pub fn add_keys_to_chain_handle<Chain: ChainHandle>(
    chain: &Chain,
    wallets: &TestWallets,
) -> Result<(), Error> {
    add_key_to_chain_handle(chain, &wallets.relayer1)?;
    add_key_to_chain_handle(chain, &wallets.relayer2)?;
    add_key_to_chain_handle(chain, &wallets.user1)?;
    add_key_to_chain_handle(chain, &wallets.user2)?;

    Ok(())
}

/**
   Generate [`ChainConfig`](ibc_relayer::config::ChainConfig) from a running
   [`FullNode`] and add it to the relayer's [`Config`].
*/
pub fn add_chain_config(config: &mut Config, running_node: &FullNode) -> Result<(), Error> {
    let chain_config = running_node.generate_chain_config()?;

    config.chains.push(chain_config);
    Ok(())
}

/**
   Save a relayer's [`Config`] to the filesystem to make it accessible
   through external CLI.

   Note that the saved config file will not be updated if the
   [`SharedConfig`] is reloaded within the test. So test authors that
   test on the config reloading functionality of the relayer would have to
   call this function again to save the updated relayer config to the
   filesystem.
*/
pub fn save_relayer_config(config: &Config, config_path: &Path) -> Result<(), Error> {
    let config_str = toml::to_string_pretty(&config)?;

    fs::write(&config_path, &config_str)?;

    info!(
        "written hermes config.toml to {}:\n{}",
        config_path.display(),
        config_str
    );

    Ok(())
}
