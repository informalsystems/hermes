/*!
   Constructs for implementing overrides for test cases.
*/

use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::config::SharedConfig;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer::supervisor::SupervisorOptions;
use ibc_relayer::supervisor::{spawn_supervisor, SupervisorHandle};

use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::base::TestConfigOverride;
use crate::framework::binary::chain::{RelayerConfigOverride, SupervisorOverride};
use crate::framework::binary::channel::{ChannelOrderOverride, PortsOverride};
use crate::framework::binary::node::NodeConfigOverride;
use crate::types::config::TestConfig;

/**
   This trait should be implemented for all test cases to allow overriding
   some parts of the behavior during the test setup.

   Since all methods in this trait have default implementation, test cases
   that do not need any override can have an empty implementation body for
   this trait.

   The trait provides generic implementation of the specialized traits such as
   [`RelayerConfigOverride`]. As a result, it is sufficient for test
   writers to only implement this trait instead of implementing the
   numerous override traits.

   When a new override trait is defined, the same trait method should
   also be defined inside this trait with a default method body.
*/
pub trait TestOverrides {
    fn modify_test_config(&self, _config: &mut TestConfig) {}

    /**
        Modify the full node config before the chain gets initialized.

        The config is in the dynamic-typed [`toml::Value`] format, as we do not
        want to model the full format of the node config in Rust. Test authors
        can use the helper methods in [`chain::config`](crate::chain::config)
        to modify common config fields.

        Implemented for [`NodeConfigOverride`].
    */
    fn modify_node_config(&self, _config: &mut toml::Value) -> Result<(), Error> {
        Ok(())
    }

    /**
       Modify the relayer config before initializing the relayer. Does no
       modification by default.

       Implemented for [`RelayerConfigOverride`].
    */
    fn modify_relayer_config(&self, _config: &mut Config) {
        // No modification by default
    }

    /**
       Optionally spawns the relayer supervisor after the relayer chain
       handles and foreign clients are initialized. Default behavior
       is to spawn the supervisor using [`spawn_supervisor`].

       Test writers can disable the spawning of supervisor by overriding
       this method and making it do nothing and return `None`.

       Implemented for [`SupervisorOverride`].
    */
    fn spawn_supervisor(
        &self,
        config: &SharedConfig,
        registry: &SharedRegistry<impl ChainHandle>,
    ) -> Result<Option<SupervisorHandle>, Error> {
        let handle = spawn_supervisor(
            config.clone(),
            registry.clone(),
            None,
            SupervisorOptions {
                health_check: false,
                force_full_scan: false,
            },
        )?;

        Ok(Some(handle))
    }

    /**
       Return the port ID used for creating the channel for the first chain.
       Returns the "transfer" port by default.

       Implemented for [`PortsOverride`].
    */
    fn channel_port_a(&self) -> PortId {
        PortId::transfer()
    }

    /**
       Return the port ID used for creating the channel for the second chain.
       Returns the "transfer" port by default.

       Implemented for [`PortsOverride`].
    */
    fn channel_port_b(&self) -> PortId {
        PortId::transfer()
    }

    fn channel_order(&self) -> Order {
        Order::Unordered
    }
}

impl<Test: TestOverrides> HasOverrides for Test {
    type Overrides = Self;

    fn get_overrides(&self) -> &Self {
        self
    }
}

impl<Test: TestOverrides> TestConfigOverride for Test {
    fn modify_test_config(&self, config: &mut TestConfig) {
        TestOverrides::modify_test_config(self, config)
    }
}

impl<Test: TestOverrides> NodeConfigOverride for Test {
    fn modify_node_config(&self, config: &mut toml::Value) -> Result<(), Error> {
        TestOverrides::modify_node_config(self, config)
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
        registry: &SharedRegistry<impl ChainHandle>,
    ) -> Result<Option<SupervisorHandle>, Error> {
        TestOverrides::spawn_supervisor(self, config, registry)
    }
}

impl<Test: TestOverrides> PortsOverride for Test {
    fn channel_port_a(&self) -> PortId {
        TestOverrides::channel_port_a(self)
    }

    fn channel_port_b(&self) -> PortId {
        TestOverrides::channel_port_b(self)
    }
}

impl<Test: TestOverrides> ChannelOrderOverride for Test {
    fn channel_order(&self) -> Order {
        TestOverrides::channel_order(self)
    }
}
