/*!
   Builder construct that spawn new chains with some common parameters.
*/

use alloc::sync::Arc;
use std::str::FromStr;

use eyre::eyre;
use ibc_relayer::config::compat_mode::CompatMode;
use tokio::runtime::Runtime;

use super::chain_type::ChainType;
use crate::{
    chain::driver::ChainDriver,
    error::Error,
    types::config::TestConfig,
    util::random::random_unused_tcp_port,
};

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
    pub command_paths: Vec<String>,

    /**
       The filesystem path to store the data files used by the chain.
    */
    pub base_store_dir: String,

    pub account_prefixes: Vec<String>,

    pub native_tokens: Vec<String>,

    pub compat_modes: Option<Vec<String>>,

    pub runtime: Arc<Runtime>,
}

impl ChainBuilder {
    /**
       Create a new `ChainBuilder`.
    */
    pub fn new(
        command_paths: Vec<String>,
        base_store_dir: &str,
        account_prefixes: Vec<String>,
        native_tokens: Vec<String>,
        compat_modes: Option<Vec<String>>,
        runtime: Arc<Runtime>,
    ) -> Self {
        Self {
            command_paths,
            base_store_dir: base_store_dir.to_string(),
            account_prefixes,
            native_tokens,
            compat_modes,
            runtime,
        }
    }

    /**
       Create a `ChainBuilder` based on the provided [`TestConfig`].
    */
    pub fn new_with_config(config: &TestConfig, runtime: Arc<Runtime>) -> Self {
        Self::new(
            config.chain_command_paths.clone(),
            &format!("{}", config.chain_store_dir.display()),
            config.account_prefixes.clone(),
            config.native_tokens.clone(),
            config.compat_modes.clone(),
            runtime,
        )
    }

    /**
       Create a new [`ChainDriver`] with the chain ID containing the
       given prefix.

       Note that this only configures the [`ChainDriver`] without
       the actual chain being initialized or spawned.

       The `ChainBuilder` will configure the [`ChainDriver`] with random
       unused ports, and add a random suffix to the chain ID.

       For example, calling this with a prefix `"alpha"` will return
       a [`ChainDriver`] configured with a chain ID  like
       `"ibc-alpha-f5a2a988"`.
    */
    pub fn new_chain(
        &self,
        prefix: &str,
        use_random_id: bool,
        chain_number: usize,
    ) -> Result<ChainDriver, Error> {
        // If there are more spawned chains than given chain binaries, take the N-th position modulo
        // the number of chain binaries given. Same for account prefix.
        let chain_number = chain_number % self.command_paths.len();
        let account_number = chain_number % self.account_prefixes.len();
        let native_token_number = chain_number % self.native_tokens.len();
        let compat_mode = if let Some(modes) = &self.compat_modes {
            let mode_str = &modes[chain_number % modes.len()];
            Some(CompatMode::from_str(mode_str).map_err(|e| {
                Error::generic(eyre!(
                    "Invalid CompatMode environment variable `{mode_str}`: {e}"
                ))
            })?)
        } else {
            None
        };

        let chain_type = ChainType::from_str(&self.command_paths[chain_number])?;

        let chain_id = chain_type.chain_id(prefix, use_random_id);

        let rpc_port = random_unused_tcp_port();
        let grpc_port = random_unused_tcp_port();
        let grpc_web_port = random_unused_tcp_port();
        let p2p_port = random_unused_tcp_port();
        let pprof_port = random_unused_tcp_port();

        let home_path = format!("{}/{}", self.base_store_dir, chain_id);

        let driver = ChainDriver::create(
            chain_type,
            self.command_paths[chain_number].clone(),
            chain_id,
            home_path,
            self.account_prefixes[account_number].clone(),
            rpc_port,
            grpc_port,
            grpc_web_port,
            p2p_port,
            pprof_port,
            self.runtime.clone(),
            self.native_tokens[native_token_number].clone(),
            compat_mode,
        )?;

        Ok(driver)
    }
}
