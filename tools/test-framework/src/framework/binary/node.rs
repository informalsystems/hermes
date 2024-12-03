/*!
   Constructs for running test cases with two full nodes
   running without setting up the relayer.
*/

use std::str::FromStr;

use toml;

use crate::bootstrap::namada::bootstrap_namada_node;
use crate::bootstrap::single::bootstrap_single_node;
use crate::chain::builder::ChainBuilder;
use crate::chain::chain_type::ChainType;
use crate::error::Error;
use crate::framework::base::HasOverrides;
use crate::framework::base::{run_basic_test, BasicTest, TestConfigOverride};
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;

/**
   Runs a test case that implements [`BinaryNodeTest`].
*/
pub fn run_binary_node_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryNodeTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides:
        NodeConfigOverride + NodeGenesisOverride + TestConfigOverride + NamadaParametersOverride,
{
    run_basic_test(&RunBinaryNodeTest { test })
}

pub fn run_single_node_test<Test, Overrides>(test: &Test) -> Result<(), Error>
where
    Test: BinaryNodeTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides:
        NodeConfigOverride + NodeGenesisOverride + TestConfigOverride + NamadaParametersOverride,
{
    run_basic_test(&RunSingleNodeTest { test })
}

/**
   This trait is implemented for test cases that need to have two full nodes
   running without the relayer being setup.

   The test case is given two [`FullNode`] which represents the two running full nodes.

   Test writers can use this to implement more advanced test cases which
   require manual setup of the relayer, so that the relayer can be started
   and stopped at a suitable time within the test.
*/
pub trait BinaryNodeTest {
    /// Test runner
    fn run(&self, config: &TestConfig, node_a: FullNode, node_b: FullNode) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override the
   full node config before the chain gets initialized.

   The config is in the dynamic-typed [`toml::Value`] format, as we do not
   want to model the full format of the node config in Rust. Test authors
   can use the helper methods in [`chain::config`](crate::chain::config)
   to modify common config fields.

   This is called by [`RunBinaryNodeTest`] before the full nodes are
   initialized and started.

   Test writers should implement
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   for their test cases instead of implementing this trait directly.
*/
pub trait NodeConfigOverride {
    /// Modify the full node config
    fn modify_node_config(&self, config: &mut toml::Value) -> Result<(), Error>;
}

/**
   An internal trait that can be implemented by test cases to override the
   genesis file before the chain gets initialized.

   The config is in the dynamic-typed [`serde_json::Value`] format, as we do not
   want to model the full format of the genesis file in Rust.

   This is called by [`RunBinaryNodeTest`] before the full nodes are
   initialized and started.

   Test writers should implement
   [`TestOverrides`](crate::framework::overrides::TestOverrides)
   for their test cases instead of implementing this trait directly.
*/
pub trait NodeGenesisOverride {
    /// Modify the genesis file
    fn modify_genesis_file(&self, genesis: &mut serde_json::Value) -> Result<(), Error>;
}

pub trait NamadaParametersOverride {
    fn namada_modify_parameter_file(&self, parameter: &mut toml::Value) -> Result<(), Error>;
}

/**
   A wrapper type that lifts a test case that implements [`BinaryNodeTest`]
   into a test case that implements [`BasicTest`].
*/
pub struct RunBinaryNodeTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

pub struct RunSingleNodeTest<'a, Test> {
    /// Inner test
    pub test: &'a Test,
}

impl<Test, Overrides> BasicTest for RunBinaryNodeTest<'_, Test>
where
    Test: BinaryNodeTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride + NamadaParametersOverride,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let command_paths_len = builder.command_paths.len();
        let node_a_type = ChainType::from_str(&builder.command_paths[0 % command_paths_len])?;
        let node_a = match node_a_type {
            ChainType::Namada => bootstrap_namada_node(
                builder,
                "a",
                false,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                |parameters| {
                    self.test
                        .get_overrides()
                        .namada_modify_parameter_file(parameters)
                },
                0,
            ),
            _ => bootstrap_single_node(
                builder,
                "1",
                config.bootstrap_with_random_ids,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                0,
            ),
        }?;
        let node_b_type = ChainType::from_str(&builder.command_paths[1 % command_paths_len])?;

        let node_b = match node_b_type {
            ChainType::Namada => bootstrap_namada_node(
                builder,
                "b",
                false,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                |parameters| {
                    self.test
                        .get_overrides()
                        .namada_modify_parameter_file(parameters)
                },
                1,
            ),
            _ => bootstrap_single_node(
                builder,
                "2",
                config.bootstrap_with_random_ids,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                1,
            ),
        }?;

        let _node_process_a = node_a.process.clone();
        let _node_process_b = node_b.process.clone();

        self.test.run(config, node_a, node_b)?;

        Ok(())
    }
}

impl<Test, Overrides> BasicTest for RunSingleNodeTest<'_, Test>
where
    Test: BinaryNodeTest,
    Test: HasOverrides<Overrides = Overrides>,
    Overrides: NodeConfigOverride + NodeGenesisOverride + NamadaParametersOverride,
{
    fn run(&self, config: &TestConfig, builder: &ChainBuilder) -> Result<(), Error> {
        let command_paths_len = builder.command_paths.len();
        let node_type = ChainType::from_str(&builder.command_paths[0 % command_paths_len])?;
        let node = match node_type {
            ChainType::Namada => bootstrap_namada_node(
                builder,
                "a",
                false,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                |parameters| {
                    self.test
                        .get_overrides()
                        .namada_modify_parameter_file(parameters)
                },
                0,
            ),
            _ => bootstrap_single_node(
                builder,
                "1",
                config.bootstrap_with_random_ids,
                |config| self.test.get_overrides().modify_node_config(config),
                |genesis| self.test.get_overrides().modify_genesis_file(genesis),
                0,
            ),
        }?;

        let _node_process = node.process.clone();

        self.test.run(config, node.clone(), node)?;

        Ok(())
    }
}

impl<Test, Overrides> HasOverrides for RunBinaryNodeTest<'_, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}

impl<Test, Overrides> HasOverrides for RunSingleNodeTest<'_, Test>
where
    Test: HasOverrides<Overrides = Overrides>,
{
    type Overrides = Overrides;

    fn get_overrides(&self) -> &Self::Overrides {
        self.test.get_overrides()
    }
}
