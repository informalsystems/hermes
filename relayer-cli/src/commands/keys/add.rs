use core::str::FromStr;
use std::{
    fs,
    path::{Path, PathBuf},
};

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{HDPath, KeyEntry, KeyRing, Store},
};

use crate::application::app_config;
use crate::conclude::Output;

/// The data structure that represents the arguments when invoking the `keys add` CLI command.
///
/// The command has one argument and two exclusive flags:
///
/// The command to add a key from a file:
///
/// `keys add [OPTIONS] --chain <CHAIN_ID> --key-file <KEY_FILE>`
///
/// The command to restore a key from a file containing mnemonic:
///
/// `keys add [OPTIONS] --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>`
///
/// The key-file and mnemonic-file flags can't be given at the same time, this will cause a terminating error.
/// If successful the key will be created or restored, depending on which flag was given.
#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct KeysAddCmd {
    #[clap(long = "chain", required = true, help = "Identifier of the chain")]
    chain_id: ChainId,

    #[clap(
        long = "key-file",
        required = true,
        value_name = "KEY_FILE",
        help = "Path to the key file",
        group = "add-restore"
    )]
    key_file: Option<PathBuf>,

    #[clap(
        long = "mnemonic-file",
        required = true,
        value_name = "MNEMONIC_FILE",
        help = "Path to file containing mnemonic to restore the key from",
        group = "add-restore"
    )]
    mnemonic_file: Option<PathBuf>,

    #[clap(
        long = "key-name",
        value_name = "KEY_NAME",
        help = "Name of the key (defaults to the `key_name` defined in the config)"
    )]
    key_name: Option<String>,

    #[clap(
        long = "hd-path",
        value_name = "HD_PATH",
        help = "Derivation path for this key",
        default_value = "m/44'/118'/0'/0/0"
    )]
    hd_path: String,
}

impl KeysAddCmd {
    fn options(&self, config: &Config) -> Result<KeysAddOptions, Box<dyn std::error::Error>> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        let name = self
            .key_name
            .clone()
            .unwrap_or_else(|| chain_config.key_name.clone());

        let hd_path = HDPath::from_str(&self.hd_path)
            .map_err(|_| format!("invalid derivation path: {}", self.hd_path))?;

        Ok(KeysAddOptions {
            config: chain_config.clone(),
            name,
            hd_path,
        })
    }
}

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub config: ChainConfig,
    pub hd_path: HDPath,
}

impl Runnable for KeysAddCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.options(&config) {
            Err(err) => Output::error(err).exit(),
            Ok(result) => result,
        };

        // Check if --key-file or --mnemonic-file was given as input.
        match (self.key_file.clone(), self.mnemonic_file.clone()) {
            (Some(key_file), _) => {
                let key = add_key(&opts.config, &opts.name, &key_file, &opts.hd_path);
                match key {
                    Ok(key) => Output::success_msg(format!(
                        "Added key '{}' ({}) on chain {}",
                        opts.name, key.account, opts.config.id
                    ))
                    .exit(),
                    Err(e) => Output::error(format!(
                        "An error occurred adding the key on chain {} from file {:?}: {}",
                        self.chain_id, key_file, e
                    ))
                    .exit(),
                }
            }
            (_, Some(mnemonic_file)) => {
                let key = restore_key(&mnemonic_file, &opts.name, &opts.hd_path, &opts.config);

                match key {
                    Ok(key) => Output::success_msg(format!(
                        "Restored key '{}' ({}) on chain {}",
                        opts.name, key.account, opts.config.id
                    ))
                    .exit(),
                    Err(e) => Output::error(format!(
                        "An error occurred restoring the key on chain {} from file {:?}: {}",
                        self.chain_id, mnemonic_file, e
                    ))
                    .exit(),
                }
            }
            // This case should never trigger.
            // The 'required' parameter for the flags will trigger an error if both flags have not been given.
            // And the 'group' parameter for the flags will trigger an error if both flags are given.
            _ => Output::error("--mnemonic-file and --key-file can't both be None".to_string())
                .exit(),
        }
    }
}

pub fn add_key(
    config: &ChainConfig,
    key_name: &str,
    file: &Path,
    hd_path: &HDPath,
) -> Result<KeyEntry, Box<dyn std::error::Error>> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;

    let key_contents = fs::read_to_string(file).map_err(|_| "error reading the key file")?;
    let key = keyring.key_from_seed_file(&key_contents, hd_path)?;

    keyring.add_key(key_name, key.clone())?;
    Ok(key)
}

pub fn restore_key(
    mnemonic: &Path,
    key_name: &str,
    hdpath: &HDPath,
    config: &ChainConfig,
) -> Result<KeyEntry, Box<dyn std::error::Error>> {
    let mnemonic_content =
        fs::read_to_string(mnemonic).map_err(|_| "error reading the mnemonic file")?;

    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    let key_entry = keyring.key_from_mnemonic(&mnemonic_content, hdpath, &config.address_type)?;

    keyring.add_key(key_name, key_entry.clone())?;
    Ok(key_entry)
}
