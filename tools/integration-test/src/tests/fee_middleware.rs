use ibc::core::ics04_channel::Version;
use ibc_test_framework::prelude::*;

#[test]
fn test_channel_with_fee() -> Result<(), Error> {
    run_binary_channel_test(&ChannelWithFeeTest)
}

pub struct ChannelWithFeeTest;

impl TestOverrides for ChannelWithFeeTest {
    fn channel_version(&self) -> Version {
        Version::ics20_with_fee()
    }
}

impl BinaryChannelTest for ChannelWithFeeTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        _chains: ConnectedChains<ChainA, ChainB>,
        _channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        Ok(())
    }
}
