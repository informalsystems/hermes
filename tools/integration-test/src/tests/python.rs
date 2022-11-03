use ibc_relayer::keyring::Store;
use ibc_test_framework::prelude::*;
use std::env;
use std::process::{Command, Stdio};

struct PythonTest;

impl TestOverrides for PythonTest {
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

impl BinaryChainTest for PythonTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        relayer: RelayerDriver,
        _chains: ConnectedChains<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let config_path = relayer
            .config_path
            .to_str()
            .ok_or_else(|| eyre!("failed to format relayer config path"))?;

        let current_dir = env::current_dir()?
            .to_str()
            .ok_or_else(|| eyre!("failed to format current directory"))?
            .to_string();

        // Use the directory where `cargo run` is called, instead of the
        // package subdirectory automatically set by cargo
        let base_dir = env::var("PWD").unwrap_or(current_dir);

        let command_args = [&format!("{}/e2e/run.py", base_dir), "-c", config_path];

        let output = Command::new("python3")
            .args(command_args)
            .current_dir(base_dir)
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .output()?;

        if output.status.success() {
            Ok(())
        } else {
            Err(Error::generic(eyre!(
                "Python E2E test exited with error code {:?}",
                output.status.code(),
            )))
        }
    }
}

#[test]
fn python_end_to_end_tests() -> Result<(), Error> {
    run_binary_chain_test(&PythonTest)
}
