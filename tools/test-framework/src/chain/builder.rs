/*!
   Builder construct that spawn new chains with some common parameters.
*/

use ibc::core::ics24_host::identifier::ChainId;

use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::types::config::TestConfig;
use crate::util::random::{random_u32, random_unused_tcp_port};

/**
   Used for holding common configuration needed to create new `ChainDriver`s.

   Currently this is hardcoded to support only a single version of Gaia chain.
   We may want to turn this into a trait in the future to support different
   chain implementations.
*/
#[derive(Debug)]
pub struct ChainBuilder {
    /**
       The CLI executable used for the chain commands. Defaults to `gaiad`.

       TODO: Have a mutable list of command paths so that the `ChainBuilder`
       may return [`ChainDriver`]s bound to different chain commands
       for testing with multiple chain implementations.
    */
    pub command_path: String,

    /**
       The filesystem path to store the data files used by the chain.
    */
    pub base_store_dir: String,
}

impl ChainBuilder {
    /**
       Create a new `ChainBuilder`.
    */
    pub fn new(command_path: &str, base_store_dir: &str) -> Self {
        Self {
            command_path: command_path.to_string(),
            base_store_dir: base_store_dir.to_string(),
        }
    }

    /**
       Create a `ChainBuilder` based on the provided [`TestConfig`].
    */
    pub fn new_with_config(config: &TestConfig) -> Self {
        Self::new(
            &config.chain_command_path,
            &format!("{}", config.chain_store_dir.display()),
        )
    }

    /**
       Create a new [`ChainDriver`] with the chain ID containing the
       given prefix.

       Note that this only configures the [`ChainDriver`] without
       the actual chain being intitialized or spawned.

       The `ChainBuilder` will configure the [`ChainDriver`] with random
       unused ports, and add a random suffix to the chain ID.

       For example, calling this with a prefix `"alpha"` will return
       a [`ChainDriver`] configured with a chain ID  like
       `"ibc-alpha-f5a2a988"`.
    */
    pub fn new_chain(&self, prefix: &str) -> Result<ChainDriver, Error> {
        let chain_num = random_u32();
        let chain_id = ChainId::from_string(&format!("ibc-{}-{:x}", prefix, chain_num));

        let rpc_port = random_unused_tcp_port();
        let grpc_port = random_unused_tcp_port();
        let grpc_web_port = random_unused_tcp_port();
        let p2p_port = random_unused_tcp_port();

        let home_path = format!("{}/{}", self.base_store_dir, chain_id);

        let driver = ChainDriver::create(
            self.command_path.clone(),
            chain_id,
            home_path,
            rpc_port,
            grpc_port,
            grpc_web_port,
            p2p_port,
        )?;

        Ok(driver)
    }
}
