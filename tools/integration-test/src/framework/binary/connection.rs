/*!
   Constructs for running test cases with two full nodes together with the
   relayer setup with chain handles and foreign clients, as well as
   connected IBC connections with completed handshakes.
*/

use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use super::chain::{
    run_binary_chain_test, BinaryChainTest, RelayerConfigOverride, SupervisorOverride,
};
use super::node::NodeConfigOverride;
use crate::bootstrap::binary::connection::bootstrap_connection;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::base::TestConfigOverride;
use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::config::TestConfig;
use crate::types::env::write_env;

/**
   Runs a test case that implements [`BinaryConnectionTest`], with
   the test case being executed twice, with the second time having the position
   of the two chains flipped.
*/
pub fn run_two_way_binary_connection_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryConnectionTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride + TestConfigOverride,
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
    Overrides: NodeConfigOverride + RelayerConfigOverride + SupervisorOverride + TestConfigOverride,
{
    run_binary_chain_test(&RunBinaryConnectionTest::new(test))
}

/**
   An owned version of [`BinaryConnectionTest`], which the test case is given
   owned [`ConnectedChains`] and [`ConnectedConnection`] values instead of just references.

   Since the test case is given full ownership, the running full node will
   and relayer will be stopped at the end of the test case.
   The test framework cannot use functions such as
   [`hang_on_error`](TestConfig::hang_on_error) to suspend
   the termination of the full nodes if the test case return errors.
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

impl<'a, Test> BinaryChainTest for RunBinaryConnectionTest<'a, Test>
where
    Test: BinaryConnectionTest,
{
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let connection = bootstrap_connection(
            &chains.client_b_to_a,
            &chains.client_a_to_b,
            config.bootstrap_with_random_ids,
        )?;

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
