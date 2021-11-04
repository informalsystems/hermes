use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;

use crate::framework::base::HasOverrides;
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::channel::PortsOverride;
use crate::relayer::supervisor::{spawn_supervisor, SupervisorHandle};

pub trait TestOverrides {
    fn modify_relayer_config(&self, _config: &mut Config) {
        // No modification by default
    }

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

impl<Test: TestOverrides> HasOverrides for Test {
    type Overrides = Self;

    fn get_overrides(&self) -> &Self {
        self
    }
}

impl<Test: TestOverrides> RelayerConfigOverride for Test {
    fn modify_relayer_config(&self, config: &mut Config) {
        TestOverrides::modify_relayer_config(self, config)
    }
}

impl<Test: TestOverrides> SupervisorOverride for Test {
    fn spawn_supervisor(
        &self,
        config: &SharedConfig,
        registry: &SharedRegistry<impl ChainHandle + 'static>,
    ) -> Option<SupervisorHandle> {
        TestOverrides::spawn_supervisor(self, config, registry)
    }
}

impl<Test: TestOverrides> PortsOverride for Test {
    fn channel_port_a(&self) -> String {
        TestOverrides::channel_port_a(self)
    }

    fn channel_port_b(&self) -> String {
        TestOverrides::channel_port_b(self)
    }
}
