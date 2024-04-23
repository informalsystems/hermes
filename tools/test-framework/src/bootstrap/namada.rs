/*!
   Helper functions for bootstrapping a single full node.
*/
use core::time::Duration;
use eyre::eyre;
use std::env;
use std::path::PathBuf;
use std::sync::{Arc, RwLock};
use toml;

use ibc_relayer::chain::namada::wallet::CliWalletUtils;
use ibc_relayer::keyring::{KeyRing, NamadaKeyPair, Store};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::chain::builder::ChainBuilder;
use crate::chain::config;
use crate::chain::exec::{simple_exec, simple_exec_with_envs};
use crate::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::prelude::{TestWallets, Wallet};
use crate::types::single::node::FullNode;
use crate::util::namada::get_namada_denom_address;

use std::fs;
use std::process::{Command, Stdio};
use std::str;
use std::thread::sleep;

use crate::types::process::ChildProcess;
use crate::util::file::pipe_to_file;

/**
   Bootstrap a single full node with the provided [`ChainBuilder`] and
   a prefix for the chain ID.

   The function would generate random postfix attached to the end of
   a chain ID. So for example having a prefix `"alpha"` may generate
   a chain with an ID  like `"ibc-alpha-f5a2a988"`

   The bootstrap function also tries to use as many random parameters
   when initializing the chain, such as using random denomination
   and wallets. This is to help ensure that the test is written to
   only work with specific hardcoded parameters.

   TODO: Due to the limitation of the `gaiad` command, currently
   parameters such as the stake denomination (`stake`) and the wallet
   address prefix (`cosmos`) cannot be overridden. It would be
   great to be able to randomize these parameters in the future
   as well.
*/
pub fn bootstrap_namada_node(
    builder: &ChainBuilder,
    prefix: &str,
    use_random_id: bool,
    config_modifier: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    _genesis_modifier: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    parameters_modifier: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    chain_number: usize,
) -> Result<FullNode, Error> {
    let namada_repo_path = env::var("NAMADA_REPO_PATH")
        .map_err(|_| Error::generic(eyre!("missing environment variable `NAMADA_REPO_PATH")))?;
    let chain_driver = builder.new_chain(prefix, use_random_id, chain_number)?;
    let home_path = &chain_driver.home_path;
    let templates_path = &format!("{home_path}/templates");
    fs::create_dir_all(templates_path)?;

    // Copy templates
    let copy_loop = format!("for file in {namada_repo_path}/genesis/localnet/*.toml; do cp \"$file\" {templates_path}; done");
    simple_exec("namada", "sh", &["-c", &copy_loop])?;

    chain_driver.update_chain_config("templates/parameters.toml", |parameters| {
        config::namada::set_default_mint_limit(parameters, 1000000000)?;
        config::namada::set_epochs_per_year(parameters, 31536)?;
        config::namada::set_default_per_epoch_throughput_limit(parameters, 10000000000)?;

        Ok(())
    })?;

    let pre_genesis_path = &format!("{home_path}/pre-genesis");
    fs::create_dir_all(pre_genesis_path)?;

    // Copy pre-genesis
    let copy_loop = format!("for file in {namada_repo_path}/genesis/localnet/src/pre-genesis/*; do cp \"$file\" {pre_genesis_path}; done");
    simple_exec("namada", "sh", &["-c", &copy_loop])?;
    simple_exec(
        "namada",
        "cp",
        &[
            "-r",
            &format!("{namada_repo_path}/genesis/localnet/src/pre-genesis/validator-0"),
            pre_genesis_path,
        ],
    )?;

    let genesis_path = &format!("{home_path}/genesis");
    fs::create_dir_all(genesis_path)?;

    let wasm_checksum = &format!("{namada_repo_path}/wasm/checksums.json");

    // Init network
    let output = simple_exec_with_envs(
        "namada",
        //&chain_driver.command_path,
        "namadac",
        &[
            //"client",
            "utils",
            "init-network",
            "--chain-prefix",
            &chain_driver.chain_id.to_string(),
            "--genesis-time",
            "2023-01-01T00:00:00Z",
            "--templates-path",
            templates_path,
            "--wasm-checksums-path",
            wasm_checksum,
            "--archive-dir",
            genesis_path,
        ],
        &[("NAMADA_BASE_DIR", home_path)],
    )?;

    let chain_id = extract_chain_id(output.stdout)?;

    let validator_base_dir = &format!("{home_path}/setup/validator-0");
    let pre_genesis_path = &format!("{home_path}/pre-genesis/validator-0");

    simple_exec_with_envs(
        &chain_id,
        //&chain_driver.command_path,
        "namadac",
        &[
            "--base-dir",
            validator_base_dir,
            //"client",
            "utils",
            "join-network",
            "--chain-id",
            &chain_id,
            "--genesis-validator",
            "validator-0",
            "--pre-genesis-path",
            pre_genesis_path,
            "--dont-prefetch-wasm",
        ],
        &[("NAMADA_NETWORK_CONFIGS_DIR", genesis_path)],
    )?;

    let chain_dir = &format!("{home_path}/{chain_id}");
    simple_exec("namada", "rm", &["-rf", chain_dir])?;

    simple_exec_with_envs(
        &chain_id,
        //&chain_driver.command_path,
        "namadac",
        &[
            //"client",
            "--base-dir",
            home_path,
            "utils",
            "join-network",
            "--chain-id",
            &chain_id,
            "--dont-prefetch-wasm",
        ],
        &[("NAMADA_NETWORK_CONFIGS_DIR", genesis_path)],
    )?;

    let dst_cp = &format!("{home_path}/setup/validator-0/{chain_id}/wasm/");

    // Copy wasm
    let copy_loop =
        format!("for file in {namada_repo_path}/wasm/*.wasm; do cp \"$file\" {dst_cp}; done");
    simple_exec("namada", "sh", &["-c", &copy_loop])?;

    let config_path = format!("{home_path}/setup/validator-0/{chain_id}/config.toml");

    chain_driver.update_chain_config(&config_path, |config| {
        config::namada::set_rpc_port(config, chain_driver.rpc_port)?;
        config::namada::set_p2p_port(config, chain_driver.p2p_port)?;
        config::namada::set_proxy_app_port(config, chain_driver.pprof_port)?;

        config_modifier(config)?;

        Ok(())
    })?;

    let parameters_path = format!("{home_path}/setup/validator-0/{chain_id}/parameters.toml");

    chain_driver.update_chain_config(&parameters_path, |parameters| {
        config::namada::set_pipeline_len(parameters, 2000)?;

        parameters_modifier(parameters)?;

        Ok(())
    })?;

    let base_args = ["--base-dir", validator_base_dir, "ledger", "run"];

    let args: Vec<&str> = base_args.to_vec();

    //let mut child = Command::new(&chain_driver.command_path)
    let mut child = Command::new("namadan")
        .args(&args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| eyre!("expected stdout to be present in child process"))?;

    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| eyre!("expected stderr to be present in child process"))?;

    let stderr_path = format!("{home_path}/stdout.log");
    let stdout_path = format!("{home_path}/stderr.log");

    pipe_to_file(stdout, &stdout_path)?;
    pipe_to_file(stderr, &stderr_path)?;

    // Wait for a while and check if the child process exited immediately.
    // If so, return error since we expect the full node to be running in the background.

    sleep(Duration::from_millis(1000));

    let status = child
        .try_wait()
        .map_err(|e| eyre!("error try waiting for child status: {}", e))?;

    let process = match status {
        None => ChildProcess::new(child),
        Some(status) => {
            let stdout_output = fs::read_to_string(stdout_path)?;
            let stderr_output = fs::read_to_string(stderr_path)?;

            return Err(eyre!(
                "expected full node process to be running, but it exited immediately with exit status {} and output: {}\n{}",
                status,
                stdout_output,
                stderr_output,
            ).into());
        }
    };

    let ks_folder = Some(format!("{}/hermes_keyring", builder.base_store_dir).into());

    let albert_key = add_namada_key(home_path, &chain_id, "albert-key", "albert", &ks_folder)?;
    let bertha_key = add_namada_key(home_path, &chain_id, "bertha-key", "bertha", &ks_folder)?;
    let christel_key =
        add_namada_key(home_path, &chain_id, "christel-key", "christel", &ks_folder)?;
    let daewon_key = add_namada_key(home_path, &chain_id, "daewon", "daewon", &ks_folder)?;

    let albert = Wallet::new_namada(
        "albert".to_string(),
        albert_key.address.to_string(),
        albert_key,
    );
    let bertha = Wallet::new_namada(
        "bertha".to_string(),
        bertha_key.address.to_string(),
        bertha_key,
    );
    let christel = Wallet::new_namada(
        "christel".to_string(),
        christel_key.address.to_string(),
        christel_key,
    );
    let daewon = Wallet::new_namada(
        "daewon".to_string(),
        daewon_key.address.to_string(),
        daewon_key,
    );

    let wallets = TestWallets {
        validator: albert,
        relayer: bertha,
        user1: christel,
        user2: daewon,
    };

    sleep(Duration::from_secs(10));

    let mut updated_chain_driver = chain_driver.clone();
    updated_chain_driver.chain_id = ChainId::from_string(&chain_id);

    let denom_str = get_namada_denom_address(&chain_id, home_path, "nam");
    let denom = Denom::base("nam", &denom_str);

    let node = FullNode {
        chain_driver: updated_chain_driver,
        denom,
        wallets,
        process: Arc::new(RwLock::new(process)),
    };

    Ok(node)
}

fn extract_chain_id(output: String) -> Result<String, Error> {
    let words: Vec<&str> = output.split_whitespace().collect();

    if let Some(derived_index) = words.iter().position(|&w| w == "Derived") {
        if let Some(&chain_id) = words.get(derived_index + 3) {
            return Ok(chain_id.to_owned());
        }
        return Err(Error::generic(eyre!(
            "chain id is not 3 words after `Derived`: {output}"
        )));
    }
    Err(Error::generic(eyre!(
        "could not find `Derived` in output: {output}"
    )))
}

fn add_namada_key(
    home_path: &str,
    chain_id: &str,
    key_name: &str,
    address_name: &str,
    ks_folder: &Option<PathBuf>,
) -> Result<NamadaKeyPair, Error> {
    let chain_id = ChainId::from_string(chain_id);
    let mut keyring = KeyRing::new_namada(Store::Test, &chain_id, ks_folder)
        .map_err(|e| Error::generic(eyre!("error creating keyring: {e}")))?;

    let key_file: PathBuf = format!("{home_path}/{chain_id}").into();

    let mut wallet = CliWalletUtils::new(key_file.to_path_buf());
    wallet
        .load()
        .map_err(|e| eyre!("error loading Namada wallet: {e}"))?;

    let secret_key = wallet
        .find_secret_key(key_name, None)
        .map_err(|e| eyre!("error loading the key from Namada wallet: {e}"))?;
    let address = wallet
        .find_address(address_name)
        .ok_or_else(|| eyre!("error loading the address from Namada wallet"))?;
    let namada_key = NamadaKeyPair {
        alias: key_name.to_string(),
        address: address.into_owned(),
        secret_key: secret_key.clone(),
    };
    keyring
        .add_key(address_name, namada_key.clone())
        .map_err(|e| Error::generic(eyre!("error adding Namada key: {e}")))?;

    Ok(namada_key)
}
