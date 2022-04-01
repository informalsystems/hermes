/*!
    Helper functions for bootstrapping two relayer chain handles
    with connected foreign clients.
*/

use eyre::Report as Error;
use ibc::core::ics24_host::identifier::ClientId;
use ibc_relayer::chain::handle::{ChainHandle, CountingAndCachingChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::error::ErrorDetail as RelayerErrorDetail;
use ibc_relayer::foreign_client::{
    extract_client_id, CreateOptions as ClientOptions, ForeignClient,
};
use ibc_relayer::keyring::errors::ErrorDetail as KeyringErrorDetail;
use ibc_relayer::registry::SharedRegistry;
use std::fs;
use std::path::Path;
use tracing::{debug, info};

use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::types::wallet::{TestWallets, Wallet};
use crate::util::random::random_u64_range;

/// A builder to bootstrap two relayer chain handles with connected
/// foreign clients.
pub struct Builder<'config> {
    test_config: &'config TestConfig,
    node_a: FullNode,
    node_b: FullNode,
    client_options_a_to_b: ClientOptions,
    client_options_b_to_a: ClientOptions,
}

impl<'config> Builder<'config> {
    /// Initializes the builder with two [`FullNode`] values representing two different
    /// running full nodes, to bootstrap chain A and chain B respectively.
    pub fn with_node_pair(
        test_config: &'config TestConfig,
        node_a: FullNode,
        node_b: FullNode,
    ) -> Self {
        Self {
            test_config,
            node_a,
            node_b,
            client_options_a_to_b: Default::default(),
            client_options_b_to_a: Default::default(),
        }
    }

    /// Work similary to [`with_node_pair`][wnp], but bootstraps a
    /// single chain to be connected with itself.
    ///
    /// Self-connected chains are in fact allowed in IBC. Although we do not
    /// have a clear use case for it yet, it is important to verify that
    /// tests that pass with two connected chains should also pass with
    /// self-connected chains.
    ///
    /// [wnp]: Builder::with_node_pair
    ///
    pub fn self_connected(test_config: &'config TestConfig, node: FullNode) -> Self {
        let node1 = node.clone();
        Self::with_node_pair(test_config, node, node1)
    }

    /// Overrides options for the foreign client connecting chain A to chain B.
    pub fn client_options_a_to_b(mut self, options: ClientOptions) -> Self {
        self.client_options_a_to_b = options;
        self
    }

    /// Overrides options for the foreign client connecting chain B to chain A.
    pub fn client_options_b_to_a(mut self, options: ClientOptions) -> Self {
        self.client_options_b_to_a = options;
        self
    }

    /// Bootstraps two relayer chain handles with connected foreign clients.
    ///
    /// Returns a tuple consisting of the [`RelayerDriver`] and a
    /// [`ConnectedChains`] object that contains the given
    /// full nodes together with the corresponding two [`ChainHandle`]s and
    /// [`ForeignClient`]s.
    pub fn bootstrap(
        self,
    ) -> Result<
        (
            RelayerDriver,
            ConnectedChains<impl ChainHandle, impl ChainHandle>,
        ),
        Error,
    > {
        self.bootstrap_with_config(|_| {})
    }

    /// Bootstraps two relayer chain handles with connected foreign clients.
    ///
    /// Returns a tuple consisting of the [`RelayerDriver`] and a
    /// [`ConnectedChains`] object that contains the given
    /// full nodes together with the corresponding two [`ChainHandle`]s and
    /// [`ForeignClient`]s.
    ///
    /// This method gives the caller a way to modify the relayer configuration
    /// that is pre-generated from the configurations of the full nodes.
    pub fn bootstrap_with_config(
        self,
        config_modifier: impl FnOnce(&mut Config),
    ) -> Result<
        (
            RelayerDriver,
            ConnectedChains<impl ChainHandle, impl ChainHandle>,
        ),
        Error,
    > {
        let mut config = Config::default();

        add_chain_config(&mut config, &self.node_a)?;
        add_chain_config(&mut config, &self.node_b)?;

        config_modifier(&mut config);

        let config_path = self.test_config.chain_store_dir.join("relayer-config.toml");

        save_relayer_config(&config, &config_path)?;

        let registry = new_registry(config.clone());

        // Pass in unique closure expressions `||{}` as the first argument so that
        // the returned chains are considered different types by Rust.
        // See [`spawn_chain_handle`] for more details.
        let handle_a = spawn_chain_handle(|| {}, &registry, &self.node_a)?;
        let handle_b = spawn_chain_handle(|| {}, &registry, &self.node_b)?;

        if self.test_config.bootstrap_with_random_ids {
            pad_client_ids(&handle_a, &handle_b)?;
            pad_client_ids(&handle_b, &handle_a)?;
        }

        let foreign_clients = ForeignClientBuilder::new(&handle_a, &handle_b)
            .client_options(self.client_options_a_to_b)
            .pair()
            .client_options(self.client_options_b_to_a)
            .bootstrap()?;

        let relayer = RelayerDriver {
            config_path,
            config,
            registry,
            hang_on_fail: self.test_config.hang_on_fail,
        };

        let chains = ConnectedChains::new(
            handle_a,
            handle_b,
            MonoTagged::new(self.node_a),
            MonoTagged::new(self.node_b),
            foreign_clients,
        );

        Ok((relayer, chains))
    }
}

pub fn pad_client_ids<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
) -> Result<(), Error> {
    let foreign_client =
        ForeignClient::restore(ClientId::default(), chain_b.clone(), chain_a.clone());

    for i in 0..random_u64_range(1, 6) {
        debug!("creating new client id {} on chain {}", i + 1, chain_b.id());
        foreign_client.build_create_client_and_send(Default::default())?;
    }

    Ok(())
}

pub struct ForeignClientBuilder<'a, ChainA: ChainHandle, ChainB: ChainHandle> {
    chain_a: &'a ChainA,
    chain_b: &'a ChainB,
    client_options: ClientOptions,
}

pub struct ForeignClientPairBuilder<'a, ChainA: ChainHandle, ChainB: ChainHandle> {
    a_to_b: ForeignClientBuilder<'a, ChainA, ChainB>,
    b_to_a_client_options: ClientOptions,
}

impl<'a, ChainA: ChainHandle, ChainB: ChainHandle> ForeignClientBuilder<'a, ChainA, ChainB> {
    pub fn new(chain_a: &'a ChainA, chain_b: &'a ChainB) -> Self {
        Self {
            chain_a,
            chain_b,
            client_options: Default::default(),
        }
    }

    pub fn client_options(mut self, settings: ClientOptions) -> Self {
        self.client_options = settings;
        self
    }

    /// Bootstrap a foreign client from `ChainA` to `ChainB`, i.e. the foreign
    /// client collects information from `ChainA` and submits them as transactions
    /// to `ChainB`.
    ///
    /// The returned `ForeignClient` is tagged in contravariant ordering, i.e.
    /// `ChainB` then `ChainB`, because `ForeignClient` takes the the destination
    /// chain in the first position.
    pub fn bootstrap(self) -> Result<ForeignClient<ChainB, ChainA>, Error> {
        bootstrap_foreign_client(self.chain_a, self.chain_b, self.client_options)
    }

    /// Continues the builder composition for a pair of clients in both directions.
    pub fn pair(self) -> ForeignClientPairBuilder<'a, ChainA, ChainB> {
        ForeignClientPairBuilder {
            a_to_b: self,
            b_to_a_client_options: Default::default(),
        }
    }
}

impl<'a, ChainA: ChainHandle, ChainB: ChainHandle> ForeignClientPairBuilder<'a, ChainA, ChainB> {
    /// Overrides the settings for a client in the reverse direction (B to A).
    pub fn client_options(mut self, settings: ClientOptions) -> Self {
        self.b_to_a_client_options = settings;
        self
    }

    pub fn bootstrap(self) -> Result<ForeignClientPair<ChainA, ChainB>, Error> {
        let chain_a = self.a_to_b.chain_a;
        let chain_b = self.a_to_b.chain_b;
        let client_a_to_b = bootstrap_foreign_client(chain_a, chain_b, self.a_to_b.client_options)?;
        let client_b_to_a = bootstrap_foreign_client(chain_b, chain_a, self.b_to_a_client_options)?;
        Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
    }
}

fn bootstrap_foreign_client<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    client_options: ClientOptions,
) -> Result<ForeignClient<ChainB, ChainA>, Error> {
    let foreign_client =
        ForeignClient::restore(ClientId::default(), chain_b.clone(), chain_a.clone());

    let event = foreign_client.build_create_client_and_send(client_options)?;
    let client_id = extract_client_id(&event)?.clone();

    info!(
        "created foreign client from chain {} to chain {} with client id {} on chain {}",
        chain_a.id(),
        chain_b.id(),
        client_id,
        chain_b.id()
    );

    Ok(ForeignClient::restore(
        client_id,
        chain_b.clone(),
        chain_a.clone(),
    ))
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
    add_key_to_chain_handle(chain, &wallets.relayer)?;
    add_key_to_chain_handle(chain, &wallets.user1)?;
    add_key_to_chain_handle(chain, &wallets.user2)?;

    Ok(())
}

/**
   Create a new [`SharedRegistry`] that uses [`CountingAndCachingChainHandle`]
   as the [`ChainHandle`] implementation.
*/
pub fn new_registry(config: Config) -> SharedRegistry<CountingAndCachingChainHandle> {
    <SharedRegistry<CountingAndCachingChainHandle>>::new(config)
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
