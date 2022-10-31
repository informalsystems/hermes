/*!
   Constructs for running test cases with two full nodes together with the
   relayer setup with chain handles and foreign clients, as well as
   connected IBC connections with completed handshakes.
*/

use core::time::Duration;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use crate::bootstrap::binary::connection::{bootstrap_connection, BootstrapConnectionOptions};
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::base::TestConfigOverride;
use crate::framework::binary::chain::{
    BinaryChainTest, ClientOptionsOverride, RelayerConfigOverride, RunBinaryChainTest,
};
use crate::framework::binary::node::{
    run_binary_node_test, NodeConfigOverride, NodeGenesisOverride,
};
use crate::framework::supervisor::{RunWithSupervisor, SupervisorOverride};
use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::config::TestConfig;
use crate::types::env::write_env;
use crate::util::suspend::hang_on_error;

/**
   Runs a test case that implements [`BinaryConnectionTest`], with
   the test case being executed twice, with the second time having the position
   of the two chains flipped.
*/
pub fn run_two_way_binary_connection_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryConnectionTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + ClientOptionsOverride
        + SupervisorOverride
        + ConnectionDelayOverride,
{
    run_binary_connection_test(&RunTwoWayBinaryConnectionTest::new(test))
}

/**
   Runs a test case that implements [`BinaryConnectionTest`].
*/
pub fn run_binary_connection_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryConnectionTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride
        + NodeConfigOverride
        + NodeGenesisOverride
        + RelayerConfigOverride
        + ClientOptionsOverride
        + SupervisorOverride
        + ConnectionDelayOverride,
{
    run_binary_node_test(&RunBinaryChainTest::new(&RunBinaryConnectionTest::new(
        &RunWithSupervisor::new(test),
    )))
}

/**
   This trait is implemented for test cases that need to have two
   full nodes running together with the relayer setup with chain
   handles and foreign clients, together with connected IBC connections
   with completed handshakes.

   Test writers can use this to implement test cases that only
   need the connection setup without the channel handshake.
*/
pub trait BinaryConnectionTest {
    /// Test runner
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override
   the connection delay parameter when creating connections.

   This is called by [`RunBinaryConnectionTest`] before creating
   the IBC connections.

  Test writers should implement
  [`TestOverrides`](crate::framework::overrides::TestOverrides)
  for their test cases instead of implementing this trait directly.
*/
pub trait ConnectionDelayOverride {
    /**
       Return the connection delay as [`Duration`].
    */
    fn connection_delay(&self) -> Duration;
}

/**
   A wrapper type that lifts a test case that implements [`BinaryConnectionTest`]
   into a test case the implements [`BinaryChainTest`].
*/
pub struct RunBinaryConnectionTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

/**
   A wrapper type that lifts a test case that implements [`BinaryConnectionTest`]
   into a test case the implements [`BinaryConnectionTest`].
*/
pub struct RunTwoWayBinaryConnectionTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test> RunBinaryConnectionTest<'a, Test>
where
    Test: BinaryConnectionTest,
{
    /// Create a new [`RunBinaryConnectionTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunTwoWayBinaryConnectionTest<'a, Test>
where
    Test: BinaryConnectionTest,
{
    /// Create a new [`BinaryConnectionTest`]
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, Overrides> BinaryChainTest for RunBinaryConnectionTest<'a, Test>
where
    Test: BinaryConnectionTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: ConnectionDelayOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let bootstrap_options = BootstrapConnectionOptions::default()
            .connection_delay(self.get_overrides().connection_delay())
            .bootstrap_with_random_ids(config.bootstrap_with_random_ids);

        let connection = bootstrap_connection(&chains.foreign_clients, bootstrap_options)?;

        let env_path = config.chain_store_dir.join("binary-connections.env");

        write_env(&env_path, &(&chains, &connection))?;

        info!("written connection environment to {}", env_path.display());

        self.test.run(config, relayer, chains, connection)?;

        Ok(())
    }
}

impl<'a, Test: BinaryConnectionTest> BinaryConnectionTest
    for RunTwoWayBinaryConnectionTest<'a, Test>
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        info!(
            "running two-way connection test, from {}/{} to {}/{}",
            chains.chain_id_a(),
            connection.connection_id_a,
            chains.chain_id_b(),
            connection.connection_id_b,
        );

        self.test
            .run(config, relayer.clone(), chains.clone(), connection.clone())?;

        info!(
            "running two-way connection test in the opposite direction, from {}/{} to {}/{}",
            chains.chain_id_b(),
            connection.connection_id_b,
            chains.chain_id_a(),
            connection.connection_id_a,
        );

        let chains = chains.flip();
        let connection = connection.flip();

        self.test.run(config, relayer, chains, connection)?;

        Ok(())
    }
}

impl<'a, Test, Overrides> BinaryConnectionTest for RunWithSupervisor<'a, Test>
where
    Test: BinaryConnectionTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: SupervisorOverride,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
        connection: ConnectedConnection<ChainA, ChainB>,
    ) -> Result<(), Error> {
        if self.get_overrides().should_spawn_supervisor() {
            relayer
                .clone()
                .with_supervisor(|| self.test.run(config, relayer, chains, connection))
        } else {
            hang_on_error(config.hang_on_fail, || {
                self.test.run(config, relayer, chains, connection)
            })
        }
    }
}

impl<'a, Test, Overrides> HasOverrides for RunBinaryConnectionTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunTwoWayBinaryConnectionTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
