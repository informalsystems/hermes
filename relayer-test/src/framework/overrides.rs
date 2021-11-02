pub fn with_overrides<Overrides, Test>(
    overrides: Overrides,
    test: Test,
) -> TestWithOverrides<Overrides, Test> {
    TestWithOverrides { overrides, test }
}

pub struct TestWithOverrides<Overrides, Test> {
    pub overrides: Overrides,
    pub test: Test,
}

pub struct OverrideNone;

pub struct OverrideAll;

pub struct OnlyOverrideRelayerConfig;

pub struct OnlyOverrideChannelPorts;

pub trait HasOverrideRelayerConfig {}

pub trait HasOverrideChannelPorts {}

impl HasOverrideRelayerConfig for OverrideAll {}
impl HasOverrideChannelPorts for OverrideAll {}
impl HasOverrideChannelPorts for OnlyOverrideChannelPorts {}
impl HasOverrideRelayerConfig for OnlyOverrideRelayerConfig {}
