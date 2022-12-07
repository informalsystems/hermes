/*!
   Definition for the test configuration.
*/

use core::fmt::Debug;
use std::path::PathBuf;

/**
   The test config to be passed to each test case. Currently this is loaded
   from the [`init_test`](crate::bootstrap::init::init_test) function
   based on the test environment variables.
*/
#[derive(Debug)]
pub struct TestConfig {
    /**
       The command that the [`ChainDriver`](crate::chain::driver::ChainDriver)
       should use to execute chain commands. Defaults to `gaiad`. This can be
       overridden with the `$CHAIN_COMMAND_PATH` environment variable.

       TODO: We might want to add a new field
       `extra_chain_command_paths: Vec<String>`
       for additional chain command paths that the `ChainDriver` can use for different
       implementations of chains to be spawned.

       For example one can list `"gaiad4"` as the main chain command and then
       `["gaiad5"]` in `extra_chain_command_paths`, so that binary chain tests
       will use `gaiad5` for the second chain being spawned.
    */
    pub chain_command_paths: Vec<String>,

    pub account_prefixes: Vec<String>,

    /**
       The directory path for storing the chain and relayer files.
       Defaults to `"data"`. This can be overridden with the `$CHAIN_STORE_DIR`
       environment variable.

       Note that this will resolve to `"relayer-test/data"` relative to the
       root project directory, as `cargo test` will automatically csuspende the
       working directory to the sub crate's directory.
    */
    pub chain_store_dir: PathBuf,

    /**
       Whether to suspend a test case when it fails whenever possible.
       Defaults to `false`. This can be overrideen by setting `HANG_ON_FAIL=1`.

       Note that even when this is enabled, not all test case will necessary
       suspend on failure. The suspend-on-failure hook is handled by individual
       test runners such as
       [`RunBinaryChainTest`](crate::framework::binary::chain::RunBinaryChainTest),
       which will suspend the test case only if the test has been setup
       successfully and only for the case when the runner holds the required
       reference for the underlying resources. Because otherwise there is
       no point suspending the test if the underlying chains or relayers are
       no longer running.
    */
    pub hang_on_fail: bool,

    pub bootstrap_with_random_ids: bool,
}
