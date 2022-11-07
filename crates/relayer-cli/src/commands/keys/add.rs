use core::str::FromStr;
use std::{
    fs,
    path::{Path, PathBuf},
};

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use eyre::eyre;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{HDPath, KeyEntry, KeyRing, Store},
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tracing::warn;

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
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
#[clap(
    override_usage = "hermes keys add [OPTIONS] --chain <CHAIN_ID> --key-file <KEY_FILE>

    hermes keys add [OPTIONS] --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>"
)]
pub struct KeysAddCmd {
    #[clap(
        long = "chain",
        required = true,
        help_heading = "FLAGS",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(
        long = "key-file",
        required = true,
        value_name = "KEY_FILE",
        help_heading = "FLAGS",
        help = "Path to the key file",
        group = "add-restore"
    )]
    key_file: Option<PathBuf>,

    #[clap(
        long = "mnemonic-file",
        required = true,
        value_name = "MNEMONIC_FILE",
        help_heading = "FLAGS",
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

    #[clap(
        long = "overwrite",
        help = "Overwrite the key if there is already one with the same key name"
    )]
    overwrite: bool,
}

impl KeysAddCmd {
    fn options(&self, config: &Config) -> eyre::Result<KeysAddOptions> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| eyre!("chain '{}' not found in configuration file", self.chain_id))?;

        let name = self
            .key_name
            .clone()
            .unwrap_or_else(|| chain_config.key_name.clone());

        let hd_path = HDPath::from_str(&self.hd_path)
            .map_err(|_| eyre!("invalid derivation path: {}", self.hd_path))?;

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
                let key = add_key(
                    &opts.config,
                    &opts.name,
                    &key_file,
                    &opts.hd_path,
                    self.overwrite,
                );
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
                let key = restore_key(
                    &mnemonic_file,
                    &opts.name,
                    &opts.hd_path,
                    &opts.config,
                    self.overwrite,
                );

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
            _ => Output::error(
                "--mnemonic-file and --key-file can't both be set or both None".to_string(),
            )
            .exit(),
        }
    }
}

pub fn add_key(
    config: &ChainConfig,
    key_name: &str,
    file: &Path,
    hd_path: &HDPath,
    overwrite: bool,
) -> eyre::Result<KeyEntry> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;

    check_key_exists(&keyring, key_name, overwrite);

    let key_contents = fs::read_to_string(file).map_err(|_| eyre!("error reading the key file"))?;
    let key = keyring.key_from_seed_file(&key_contents, hd_path)?;

    keyring.add_key(key_name, key.clone())?;
    Ok(key)
}

pub fn restore_key(
    mnemonic: &Path,
    key_name: &str,
    hdpath: &HDPath,
    config: &ChainConfig,
    overwrite: bool,
) -> eyre::Result<KeyEntry> {
    let mnemonic_content =
        fs::read_to_string(mnemonic).map_err(|_| eyre!("error reading the mnemonic file"))?;

    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;

    check_key_exists(&keyring, key_name, overwrite);

    let key_entry = keyring.key_from_mnemonic(&mnemonic_content, hdpath, &config.address_type)?;

    keyring.add_key(key_name, key_entry.clone())?;
    Ok(key_entry)
}

/// Check if the key with the given key name already exists.
/// If it already exists and overwrite is false, abort the command with an error.
/// If overwrite is true, output a warning message informing the key will be overwritten.
fn check_key_exists(keyring: &KeyRing, key_name: &str, overwrite: bool) {
    if keyring.get_key(key_name).is_ok() {
        if overwrite {
            warn!("key {} will be overwritten", key_name);
        } else {
            Output::error(format!("A key with name '{}' already exists", key_name)).exit();
        }
    }
}

#[cfg(test)]
mod tests {

    use super::KeysAddCmd;
    use std::path::PathBuf;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_keys_add_key_file() {
        assert_eq!(
            KeysAddCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_file: Some(PathBuf::from("key_file")),
                mnemonic_file: None,
                key_name: None,
                hd_path: "m/44'/118'/0'/0/0".to_string(),
                overwrite: false,
            },
            KeysAddCmd::parse_from(["test", "--chain", "chain_id", "--key-file", "key_file"])
        )
    }

    #[test]
    fn test_keys_add_mnemonic_file() {
        assert_eq!(
            KeysAddCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_file: None,
                mnemonic_file: Some(PathBuf::from("mnemonic_file")),
                key_name: None,
                hd_path: "m/44'/118'/0'/0/0".to_string(),
                overwrite: false
            },
            KeysAddCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--mnemonic-file",
                "mnemonic_file"
            ])
        )
    }

    #[test]
    fn test_keys_add_key_file_overwrite() {
        assert_eq!(
            KeysAddCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_file: Some(PathBuf::from("key_file")),
                mnemonic_file: None,
                key_name: None,
                hd_path: "m/44'/118'/0'/0/0".to_string(),
                overwrite: true,
            },
            KeysAddCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--key-file",
                "key_file",
                "--overwrite"
            ])
        )
    }

    #[test]
    fn test_keys_add_mnemonic_file_overwrite() {
        assert_eq!(
            KeysAddCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_file: None,
                mnemonic_file: Some(PathBuf::from("mnemonic_file")),
                key_name: None,
                hd_path: "m/44'/118'/0'/0/0".to_string(),
                overwrite: true,
            },
            KeysAddCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--mnemonic-file",
                "mnemonic_file",
                "--overwrite"
            ])
        )
    }

    #[test]
    fn test_keys_add_no_file_nor_mnemonic() {
        assert!(KeysAddCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err());
    }

    #[test]
    fn test_keys_add_key_and_mnemonic() {
        assert!(KeysAddCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--key-file",
            "key_file",
            "--mnemonic-file",
            "mnemonic_file"
        ])
        .is_err());
    }

    #[test]
    fn test_keys_add_no_chain() {
        assert!(KeysAddCmd::try_parse_from(["test", "--key-file", "key_file"]).is_err());
    }
}
