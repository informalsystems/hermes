//! An MVP test for demonstration purposes.
//!
//! You can find more thorough documentation on this example
//! test at `tools/test-framework/src/docs/walkthroughs/simple.rs`.

use ibc_test_framework::prelude::*;

#[test]
pub fn example_test() -> Result<(), Error> {
    run_binary_channel_test(&ExampleTest)
}

pub struct ExampleTest;

impl TestOverrides for ExampleTest {}

impl BinaryChannelTest for ExampleTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        _chains: ConnectedChains<ChainA, ChainB>,
        _channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        suspend()
    }
}
