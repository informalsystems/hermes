use ibc_test_framework::prelude::*;
use ibc_test_framework::types::nary::connection::ConnectedConnections;

#[test]
fn test_example() -> Result<(), Error> {
    run_nary_connection_test(&ExampleTest)
}
pub struct ExampleTest;

impl TestOverrides for ExampleTest {}

impl NaryConnectionTest<4> for ExampleTest {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        _chains: NaryConnectedChains<Handle, 4>,
        connections: ConnectedConnections<Handle, 4>,
    ) -> Result<(), Error> {
        let connection_0_to_1 = connections.connection_at::<0, 1>()?;
        let connection_1_to_0 = connections.connection_at::<1, 0>()?;

        let connection_1_to_2 = connections.connection_at::<1, 2>()?;
        let connection_2_to_1 = connections.connection_at::<2, 1>()?;

        let connection_2_to_3 = connections.connection_at::<2, 3>()?;
        let connection_3_to_2 = connections.connection_at::<3, 2>()?;

        info!("Connection from 0 to 1: {connection_0_to_1:#?}");
        info!("Connection from 1 to 0: {connection_1_to_0:#?}");

        info!("Connection from 1 to 2: {connection_1_to_2:#?}");
        info!("Connection from 2 to 1: {connection_2_to_1:#?}");

        info!("Connection from 2 to 3: {connection_2_to_3:#?}");
        info!("Connection from 3 to 2: {connection_3_to_2:#?}");

        panic!("The test needs to fail to block when running with HANG_ON_FAIL=1");
    }
}
