/*!
    A quick demo of how a test with full setup can be written.

    ```rust
    # use ibc_integration_test::prelude::*;

    #[test]
    pub fn example_test() -> Result<(), Error> {
        run_binary_channel_test(&ExampleTest)
    }

    pub struct ExampleTest;

    impl TestOverrides for ExampleTest {}

    impl BinaryChannelTest for ExampleTest {
        fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
            &self,
            _config: &TestConfig,
            _relayer: RelayerDriver,
            _chains: ConnectedChains<ChainA, ChainB>,
            _channel: ConnectedChannel<ChainA, ChainB>,
        ) -> Result<(), Error> {
            suspend()
        }
    }
    ```

    We first define an empty struct [`ExampleTest`] to represent our test case.
    We then implement the
    [`BinaryChannelTest`](ibc_test_framework::framework::binary::channel::BinaryChannelTest)
    trait so that the test framework sets up the relayer with two chains
    running together with connected channels.

    Inside our test, we simply call the [`suspend`] function to
    suspend the test indefinitely. While this means that the test would never
    pass, we can use this as a starting point to do _manual testing_ with the
    chains that have been setup by the test, and figure out how to continue
    writing our test.

    We also implement [`TestOverrides`] for [`ExampleTest`] with an empty body.
    The [`TestOverrides`] trait allows us to override some behavior of the
    test case by implement methods that override the default behavior.

    Finally, we define the `example_test` function with the `#[test]` pragma
    as the entry point for Rust to execute the test. We call the runner function
    [`run_binary_channel_test`](ibc_test_framework::framework::binary::channel::run_binary_channel_test),
    which accepts a reference to any struct implementing
    [`BinaryChannelTest`](ibc_test_framework::framework::binary::channel::BinaryChannelTest)
    and run the test for us.

    By convention, the tests written are placed in the [`tests`](ibc_test_framework::tests)
    module. We can then run the test on the command line such as follows:

    ```bash
    RUST_LOG=info RUST_BACKTRACE=1 \
        cargo test -p ibc-relayer-test --features example -- --test-threads=1 \
        example_test
    ```

    We use the environment variables `RUST_LOG` to control the log level,
    and `RUST_BACKTRACE` to display backtrace when errors occurred.
    The test flag `--test-threads=1` is set so that Rust do not run multiple
    tests in parallel, as it can make it difficult to follow the logs.
    See [TestConfig](ibc_test_framework::types::config::TestConfig) for more information
    about configuring how the tests should be run.

    For this example, we disable the test from running by default, since
    it uses [`suspend`] and is never going to pass. Here we explicitly pass
    `--features example` so that the `example` feature is activated and this
    test will run. Finally we specify the name of the test, which in our case
    is `example_test`, so that only that test is being run.

    After starting the test, we may see the logs such as following shown:

    ```text
    $ cargo test -p ibc-integration-test --features example -- --nocapture --test-threads=1 example_test
    ...
    INFO created new chain/client/connection/channel from ibc-alpha-c4aed8f9/07-tendermint-4/connection-6/channel-1 to ibc-beta-fcb867bb/07-tendermint-6/connection-1/channel-6
    INFO written channel environment to /path/to/ibc-rs/tools/integration-test/data/test-1094235493/binary-channels.env
    WARN suspending the test indefinitely. you can still interact with any spawned chains and relayers
    ...
    ```

    Near the last line of the logs, you can find in the logs information about
    the path to the environment variables exported by the test.  you can also
    find a warning that states that the test have been suspended indefinitely.
    We can also notice that the chains are created with random IDs and
    listening on random ports.

    Using the log information, we can for example use `gaiad` to query for
    the balance of the accounts created by the test by running something like:

    ```bash
    $ source /path/to/ibc-rs/tools/integration-test/data/test-1094235493/binary-channels.env
    $ gaiad --home "$NODE_A_HOME" --node $NODE_A_RPC_ADDR query bank balances $NODE_A_WALLETS_USER1_ADDRESS
    balances:
    - amount: "6902395390297"
    denom: coin95143d31
    - amount: "6902395390297"
    denom: stake
    pagination:
    next_key: null
    total: "0"
    ```

    The test data and configuration files are stored at the absolute path shown
    in the log, which looks something like
    `/path/to/ibc-rs/tools/integration-test/data/test-1094235493`.
    The sub-directory `test-1094235493` is randomly generated at the beginning
    of a test case, so that all data related to that test case belongs to the
    same directory.
*/

use ibc_test_framework::prelude::*;

#[test]
pub fn example_test() -> Result<(), Error> {
    run_binary_channel_test(&ExampleTest)
}

pub struct ExampleTest;

impl TestOverrides for ExampleTest {}

impl BinaryChannelTest for ExampleTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        _chains: ConnectedChains<ChainA, ChainB>,
        _channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        relayer.with_supervisor(suspend)
    }
}
