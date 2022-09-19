/*!
   Constructs for running test cases with more than two chains,
   together with the relayer setup with chain handles and foreign clients.
*/

use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use crate::bootstrap::nary::chain::{
    boostrap_chains_with_nodes, boostrap_chains_with_self_connected_node,
};
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::framework::binary::chain::RelayerConfigOverride;
use crate::framework::binary::node::{NodeConfigOverride, NodeGenesisOverride};
use crate::framework::nary::node::{run_nary_node_test, NaryNodeTest};
use crate::framework::supervisor::{RunWithSupervisor, SupervisorOverride};
use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::DropChainHandle;
use crate::types::config::TestConfig;
use crate::types::env::write_env;
use crate::types::nary::chains::NaryConnectedChains;
use crate::types::single::node::FullNode;
use crate::util::suspend::hang_on_error;

/**
   Runs a test case that implements [`NaryChainTest`] with a `SIZE` number of
   chains bootstrapped.

   Note that the test may take more time as the number of chains increase,
   as the required connections would increase exponentially. For each
   new chain added, a self-connected foreign client is also created.

   Following shows a quick idea of how many connections are needed for each
   new chain added:

   1. 0-0
   2. 0-0, 0-1, 1-1
   3. 0-0, 0-1, 0-2, 1-1, 1-2, 2-2
   4. 0-0, 0-1, 0-2, 0-3, 1-1, 1-2, 1-3, 2-2, 2-3, 3-3
   5. ...
*/
pub fn run_nary_chain_test<Test, Overrides, const SIZE: usize>(test: &Test) -> Result<(), Error>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + SupervisorOverride,
{
    run_nary_node_test(&RunNaryChainTest::new(&RunWithSupervisor::new(test)))
}

/**
    Runs a test case that implements [`NaryChainTest`], with one self-connected chain used
    to emulate many connnections.

    This works because IBC allows a chain to connect back to itself without the chain
    knowing it. Using this, we can emulate N-ary chain tests using only one chain
    and save the performance overhead of spawning many chains.

    Note that with this, there is still performance overhead of establishing
    new connections and channels for each position, as otherwise the transferred
    IBC denoms will get mixed up. Some test cases also may not able to make
    use of self connected chains, e.g. if they need to start and stop individual
    chains.
*/
pub fn run_self_connected_nary_chain_test<Test, Overrides, const SIZE: usize>(
    test: &Test,
) -> Result<(), Error>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + SupervisorOverride,
{
    run_nary_node_test(&RunSelfConnectedNaryChainTest::new(
        &RunWithSupervisor::new(test),
    ))
}

/**
    This trait is implemented for test cases that need to have more than
    two chains running.

    Test writers can use this to implement test cases that only
    need the chains and relayers setup without the connection or
    channel handshake.
*/
pub trait NaryChainTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, SIZE>,
    ) -> Result<(), Error>;
}

/**
    A wrapper type that lifts a test case that implements [`RunNaryChainTest`]
    into a test case the implements [`NaryNodeTest`].
*/
pub struct RunNaryChainTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

/**
    A wrapper type that lifts a test case that implements [`RunNaryChainTest`]
    into a test case the implements [`NaryNodeTest<1>`]. i.e. only one underlying
    full node is spawned to emulate all chains.
*/
pub struct RunSelfConnectedNaryChainTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, Overrides, const SIZE: usize> NaryNodeTest<SIZE> for RunNaryChainTest<'a, Test, SIZE>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride,
{
    fn run(&self, config: &TestConfig, nodes: [FullNode; SIZE]) -> Result<(), Error> {
        let (relayer, chains) = boostrap_chains_with_nodes(config, nodes, |config| {
            self.test.get_overrides().modify_relayer_config(config);
        })?;

        let env_path = config.chain_store_dir.join("nary-chains.env");

        write_env(&env_path, &(&relayer, &chains))?;

        info!("written chains environment to {}", env_path.display());

        let _drop_handles = chains
            .chain_handles()
            .iter()
            .map(|handle| DropChainHandle(handle.clone()))
            .collect::<Vec<_>>();

        self.test.run(config, relayer, chains)?;

        Ok(())
    }
}

impl<'a, Test, Overrides, const SIZE: usize> NaryNodeTest<1>
    for RunSelfConnectedNaryChainTest<'a, Test, SIZE>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: RelayerConfigOverride,
{
    fn run(&self, config: &TestConfig, nodes: [FullNode; 1]) -> Result<(), Error> {
        let (relayer, chains) =
            boostrap_chains_with_self_connected_node(config, nodes[0].clone(), |config| {
                self.test.get_overrides().modify_relayer_config(config);
            })?;

        let env_path = config.chain_store_dir.join("nary-chains.env");

        write_env(&env_path, &(&relayer, &chains))?;

        info!("written chains environment to {}", env_path.display());

        let _drop_handles = chains
            .chain_handles()
            .iter()
            .map(|handle| DropChainHandle(handle.clone()))
            .collect::<Vec<_>>();

        self.test.run(config, relayer, chains)?;

        Ok(())
    }
}

impl<'a, Test, Overrides, const SIZE: usize> NaryChainTest<SIZE> for RunWithSupervisor<'a, Test>
where
    Test: NaryChainTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: SupervisorOverride,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, SIZE>,
    ) -> Result<(), Error> {
        if self.get_overrides().should_spawn_supervisor() {
            relayer
                .clone()
                .with_supervisor(|| self.test.run(config, relayer, chains))
        } else {
            hang_on_error(config.hang_on_fail, || {
                self.test.run(config, relayer, chains)
            })
        }
    }
}

impl<'a, Test, const SIZE: usize> RunNaryChainTest<'a, Test, SIZE>
where
    Test: NaryChainTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, const SIZE: usize> RunSelfConnectedNaryChainTest<'a, Test, SIZE>
where
    Test: NaryChainTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides for RunNaryChainTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides
    for RunSelfConnectedNaryChainTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
