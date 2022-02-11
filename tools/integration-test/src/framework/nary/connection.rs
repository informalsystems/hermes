use ibc_relayer::chain::handle::ChainHandle;

use crate::bootstrap::nary::connection::bootstrap_connections;
use crate::error::Error;
use crate::framework::base::{HasOverrides, TestConfigOverride};
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::connection::BinaryConnectionTest;
use crate::framework::binary::node::NodeConfigOverride;
use crate::relayer::driver::RelayerDriver;
use crate::types::config::TestConfig;
use crate::types::nary::chains::ConnectedChains;
use crate::types::nary::connection::ConnectedConnections;

use super::chain::{run_nary_chain_test, NaryChainTest};

pub fn run_nary_connection_test<Test, Overrides, const SIZE: usize>(
    test: &Test,
) -> Result<(), Error>
where
    Test: NaryConnectionTest<SIZE>,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: TestConfigOverride + NodeConfigOverride + RelayerConfigOverride + SupervisorOverride,
{
    run_nary_chain_test(&RunNaryConnectionTest::new(test))
}

pub trait NaryConnectionTest<const SIZE: usize> {
    /// Test runner
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Handle, SIZE>,
        connections: ConnectedConnections<Handle, SIZE>,
    ) -> Result<(), Error>;
}

pub struct RunNaryConnectionTest<'a, Test, const SIZE: usize> {
    /// Inner test
    pub test: &'a Test,
}

pub struct RunBinaryAsNaryConnectionTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<'a, Test, const SIZE: usize> RunNaryConnectionTest<'a, Test, SIZE>
where
    Test: NaryConnectionTest<SIZE>,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test> RunBinaryAsNaryConnectionTest<'a, Test>
where
    Test: BinaryConnectionTest,
{
    pub fn new(test: &'a Test) -> Self {
        Self { test }
    }
}

impl<'a, Test, const SIZE: usize> NaryChainTest<SIZE> for RunNaryConnectionTest<'a, Test, SIZE>
where
    Test: NaryConnectionTest<SIZE>,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Handle, SIZE>,
    ) -> Result<(), Error> {
        let connections = bootstrap_connections(
            chains.foreign_clients.clone(),
            config.bootstrap_with_random_ids,
        )?;

        self.test.run(config, relayer, chains, connections)?;

        Ok(())
    }
}

impl<'a, Test> NaryConnectionTest<2> for RunBinaryAsNaryConnectionTest<'a, Test>
where
    Test: BinaryConnectionTest,
{
    fn run<Handle: ChainHandle>(
        &self,
        config: &TestConfig,
        relayer: RelayerDriver,
        chains: ConnectedChains<Handle, 2>,
        connections: ConnectedConnections<Handle, 2>,
    ) -> Result<(), Error> {
        self.test
            .run(config, relayer, chains.into(), connections.into())
    }
}

impl<'a, Test, Overrides, const SIZE: usize> HasOverrides for RunNaryConnectionTest<'a, Test, SIZE>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<'a, Test, Overrides> HasOverrides for RunBinaryAsNaryConnectionTest<'a, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
