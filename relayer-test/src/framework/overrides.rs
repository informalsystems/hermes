use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;

use crate::framework::binary::chain::{TestWithRelayerConfigOverride, TestWithSupervisorOverride};
use crate::framework::binary::channel::TestWithChannelPortsOverride;
use crate::relayer::supervisor::{spawn_supervisor, SupervisorHandle};

pub fn default_overrides() -> impl AllTestOverrides {
    WithOverrides {
        overrides: &DefaultOverrides,
    }
}

pub fn with_overrides<'a, Overrides: TestOverrides>(
    overrides: &'a Overrides,
) -> impl AllTestOverrides + 'a {
    WithOverrides { overrides }
}

pub struct DefaultOverrides;

pub struct WithOverrides<'a, Overrides> {
    pub overrides: &'a Overrides,
}

pub trait AllTestOverrides:
    TestWithRelayerConfigOverride + TestWithSupervisorOverride + TestWithChannelPortsOverride
{
}

pub trait TestOverrides {
    fn modify_relayer_config(&self, _config: &mut Config) {}

    fn spawn_supervisor(
        &self,
        config: &SharedConfig,
        registry: &SharedRegistry<impl ChainHandle + 'static>,
    ) -> Option<SupervisorHandle> {
        let handle = spawn_supervisor(config.clone(), registry.clone());
        Some(handle)
    }

    fn channel_port_a(&self) -> String {
        "transfer".to_string()
    }

    fn channel_port_b(&self) -> String {
        "transfer".to_string()
    }
}

impl TestOverrides for DefaultOverrides {}

impl<Overrides> AllTestOverrides for Overrides where
    Overrides:
        TestWithRelayerConfigOverride + TestWithSupervisorOverride + TestWithChannelPortsOverride
{
}

impl<'a, Overrides: TestOverrides> TestWithRelayerConfigOverride for WithOverrides<'a, Overrides> {
    fn modify_relayer_config(&self, config: &mut Config) {
        self.overrides.modify_relayer_config(config)
    }
}

impl<'a, Overrides: TestOverrides> TestWithSupervisorOverride for WithOverrides<'a, Overrides> {
    fn spawn_supervisor(
        &self,
        config: &SharedConfig,
        registry: &SharedRegistry<impl ChainHandle + 'static>,
    ) -> Option<SupervisorHandle> {
        self.overrides.spawn_supervisor(config, registry)
    }
}

impl<'a, Overrides: TestOverrides> TestWithChannelPortsOverride for WithOverrides<'a, Overrides> {
    fn channel_port_a(&self) -> String {
        self.overrides.channel_port_a()
    }

    fn channel_port_b(&self) -> String {
        self.overrides.channel_port_b()
    }
}
