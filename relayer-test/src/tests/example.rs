use crate::prelude::*;

struct ExampleTest;

impl TestOverrides for ExampleTest {}

impl BinaryChannelTest for ExampleTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _chains: &ConnectedChains<ChainA, ChainB>,
        _channel: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        hang()
    }
}

#[test]
fn example_test() -> Result<(), Error> {
    run_binary_channel_test(&ExampleTest)
}
