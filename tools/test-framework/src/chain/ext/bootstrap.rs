use core::str::FromStr;

use eyre::eyre;
use serde_json as json;
use std::fs;
use std::path::PathBuf;
use std::str;
use toml;
use tracing::debug;

use ibc_relayer::keyring::{HDPath, KeyEntry};

use crate::chain::cli::bootstrap::{
    add_genesis_account, add_genesis_validator, add_wallet, collect_gen_txs, initialize,
    start_chain,
};
use crate::chain::driver::ChainDriver;
use crate::error::{handle_generic_error, Error};
use crate::ibc::token::Token;
use crate::types::process::ChildProcess;
use crate::types::wallet::{Wallet, WalletAddress, WalletId};

pub trait ChainBootstrapMethodsExt {
    /**
       Read the content at a file path relative to the chain home
       directory, and return the result as a string.

       This is not efficient but is sufficient for testing purposes.
    */
    fn read_file(&self, file_path: &str) -> Result<String, Error>;

    /**
       Write the string content to a file path relative to the chain home
       directory.

       This is not efficient but is sufficient for testing purposes.
    */
    fn write_file(&self, file_path: &str, content: &str) -> Result<(), Error>;

    /**
       Modify the Gaia chain config which is saved in toml format.
    */
    fn update_chain_config(
        &self,
        file: &str,
        cont: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    ) -> Result<(), Error>;

    /**
       Initialized the chain data stores.

       This is used by
       [`bootstrap_single_node`](crate::bootstrap::single::bootstrap_single_node).
    */
    fn initialize(&self) -> Result<(), Error>;

    /**
       Modify the Gaia genesis file.
    */
    fn update_genesis_file(
        &self,
        file: &str,
        cont: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    ) -> Result<(), Error>;

    /**
       Add a wallet with the given ID to the full node's keyring.
    */
    fn add_wallet(&self, wallet_id: &str) -> Result<Wallet, Error>;

    /**
       Add a wallet address to the genesis account list for an uninitialized
       full node.
    */
    fn add_genesis_account(&self, wallet: &WalletAddress, amounts: &[&Token]) -> Result<(), Error>;

    /**
       Add a wallet ID with the given stake amount to be the genesis validator
       for an uninitialized chain.
    */
    fn add_genesis_validator(&self, wallet_id: &WalletId, token: &Token) -> Result<(), Error>;

    /**
       Call `gaiad collect-gentxs` to generate the genesis transactions.
    */
    fn collect_gen_txs(&self) -> Result<(), Error>;

    /**
       Start a full node by running in the background `gaiad start`.

       Returns a [`ChildProcess`] that stops the full node process when the
       value is dropped.
    */
    fn start(&self) -> Result<ChildProcess, Error>;
}

impl ChainBootstrapMethodsExt for ChainDriver {
    fn read_file(&self, file_path: &str) -> Result<String, Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let res = fs::read_to_string(full_path)?;
        Ok(res)
    }

    fn write_file(&self, file_path: &str, content: &str) -> Result<(), Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let full_path_str = format!("{}", full_path.display());
        fs::write(full_path, content)?;
        debug!("created new file {:?}", full_path_str);
        Ok(())
    }

    fn update_chain_config(
        &self,
        file: &str,
        cont: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let config_path = format!("config/{}", file);

        let config1 = self.read_file(&config_path)?;

        let mut config2 = toml::from_str(&config1).map_err(handle_generic_error)?;

        cont(&mut config2)?;

        let config3 = toml::to_string_pretty(&config2).map_err(handle_generic_error)?;

        self.write_file(&config_path, &config3)?;

        Ok(())
    }

    fn initialize(&self) -> Result<(), Error> {
        initialize(self.chain_id.as_str(), &self.command_path, &self.home_path)
    }

    fn update_genesis_file(
        &self,
        file: &str,
        cont: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let config1 = self.read_file(&format!("config/{}", file))?;

        let mut config2 = serde_json::from_str(&config1).map_err(handle_generic_error)?;

        cont(&mut config2)?;

        let config3 = serde_json::to_string_pretty(&config2).map_err(handle_generic_error)?;

        self.write_file("config/genesis.json", &config3)?;

        Ok(())
    }

    fn add_wallet(&self, wallet_id: &str) -> Result<Wallet, Error> {
        let seed_content = add_wallet(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            wallet_id,
        )?;

        let json_val: json::Value = json::from_str(&seed_content).map_err(handle_generic_error)?;

        let wallet_address = json_val
            .get("address")
            .ok_or_else(|| eyre!("expect address string field to be present in json result"))?
            .as_str()
            .ok_or_else(|| eyre!("expect address string field to be present in json result"))?
            .to_string();

        let seed_path = format!("{}-seed.json", wallet_id);
        self.write_file(&seed_path, &seed_content)?;

        let hd_path = HDPath::from_str(self.chain_type.hd_path())
            .map_err(|e| eyre!("failed to create HDPath: {:?}", e))?;

        let key =
            KeyEntry::from_seed_file(&seed_content, &hd_path).map_err(handle_generic_error)?;

        Ok(Wallet::new(wallet_id.to_string(), wallet_address, key))
    }

    fn add_genesis_account(&self, wallet: &WalletAddress, amounts: &[&Token]) -> Result<(), Error> {
        let amounts_str = amounts.iter().map(|t| t.to_string()).collect::<Vec<_>>();

        add_genesis_account(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &wallet.0,
            &amounts_str,
        )
    }

    fn add_genesis_validator(&self, wallet_id: &WalletId, token: &Token) -> Result<(), Error> {
        add_genesis_validator(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &wallet_id.0,
            &token.to_string(),
        )
    }

    fn collect_gen_txs(&self) -> Result<(), Error> {
        collect_gen_txs(self.chain_id.as_str(), &self.command_path, &self.home_path)
    }

    fn start(&self) -> Result<ChildProcess, Error> {
        let extra_start_args = self.chain_type.extra_start_args();

        start_chain(
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            &self.grpc_listen_address(),
            &extra_start_args
                .iter()
                .map(|s| s.as_ref())
                .collect::<Vec<_>>(),
        )
    }
}
