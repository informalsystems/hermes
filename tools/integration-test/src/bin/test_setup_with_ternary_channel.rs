/*!
    This is a simple wrapper around [`BinaryChannelTest`] and turn it into
    an executable that can be used for manual testing with two test chains
    with connected channel being setup.

    When the command is executed, you should see log messages such as
    following near the end:

    ```bash
    $ cargo run --bin test_setup_with_binary_channel
    ...
    INFO ibc_integration_test::framework::binary::channel: written channel environment to /path/to/ibc-rs/data/test-3742758098/binary-channels.env
    WARN ibc_integration_test::util::suspend: suspending the test indefinitely. you can still interact with any spawned chains and relayers
    ```

    The `binary-channels.env` file generated contains the environment variables
    that are essential for accessing the test chains. You can source it and
    run the relayer commands in a separate terminal such as:

    ```bash
    $ source /path/to/ibc-rs/data/test-1790156739/binary-channels.env
    $ cargo run --bin hermes -- -c $RELAYER_CONFIG tx ft-transfer \
        $CHAIN_ID_B $CHAIN_ID_A $PORT_A $CHANNEL_ID_A 9999 -o 1000 \
        -k $NODE_A_WALLETS_USER1_KEY_ID -d $NODE_A_DENOM
    ```
*/

use ibc_relayer::keyring::Store;
use ibc_test_framework::prelude::*;
use std::env;
use std::path::PathBuf;

struct Test {
    store_dir: PathBuf,
}

impl TestOverrides for Test {
    fn modify_test_config(&self, config: &mut TestConfig) {
        config.chain_store_dir = self.store_dir.clone();
    }

    fn modify_relayer_config(&self, config: &mut Config) {
        for mut chain in config.chains.iter_mut() {
            // Modify the key store type to `Store::Test` so that the wallet
            // keys are stored to ~/.hermes/keys so that we can use them
            // with external relayer commands.
            chain.key_store_type = Store::Test;
        }
    }

    fn should_spawn_supervisor(&self) -> bool {
        false
    }
}

impl NaryChannelTest<3> for Test {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        _chains: NaryConnectedChains<Handle, 3>,
        _channels: NaryConnectedChannels<Handle, 3>,
    ) -> Result<(), Error> {
        suspend()
    }
}

impl PortsOverride<3> for Test {}

fn main() -> Result<(), Error> {
    let store_dir = env::var("TEST_STORE_DIR").unwrap_or_else(|_| "data/test".to_string());

    println!(
        "Setting up binary channel test environment at {}. (Overridable with $TEST_STORE_DIR)",
        store_dir
    );

    println!("Make sure the directory is clean for the setup to succeed");

    run_nary_channel_test(&Test {
        store_dir: store_dir.into(),
    })
}
