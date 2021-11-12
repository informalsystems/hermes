/*!
   Implementation of [`ChainDriver`].
*/

use core::str::FromStr;
use core::time::Duration;
use eyre::eyre;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::keyring::{HDPath, KeyEntry, KeyFile};
use serde_json as json;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::str;
use toml;
use tracing::{debug, trace};

use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::process::ChildProcess;
use crate::types::wallet::{Wallet, WalletAddress, WalletId};
use crate::util::file::pipe_to_file;
use crate::util::random::random_u32;
use crate::util::retry::assert_eventually_succeed;

pub mod query_txs;
pub mod tagged;
pub mod transfer;

const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";

/**
    A driver for interacting with a chain full nodes through command line.

    The name `ChainDriver` is inspired by
    [WebDriver](https://developer.mozilla.org/en-US/docs/Web/WebDriver),
    which is the term used to describe programs that control spawning of the
    web browsers. In our case, the ChainDriver is used to spawn and manage
    chain full nodes.

    Currently the `ChainDriver` is hardcoded to support only a single version
    of Gaia chain. In the future, we will want to turn this into one or more
    `ChainDriver` traits so that they can be used to spawn multiple chain
    implementations other than a single version of Gaia.
*/

#[derive(Debug, Clone)]
pub struct ChainDriver {
    /**
       The filesystem path to the Gaia CLI. Defaults to `gaiad`.
    */
    pub command_path: String,

    /**
       The ID of the chain.
    */
    pub chain_id: ChainId,

    /**
       The home directory for the full node to store data files.
    */
    pub home_path: String,

    /**
       The port used for RPC.
    */
    pub rpc_port: u16,

    /**
       The port used for GRPC.
    */
    pub grpc_port: u16,

    /**
       The port used for P2P. (Currently unused other than for setup)
    */
    pub p2p_port: u16,
}

impl ExportEnv for ChainDriver {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("CMD", &self.command_path);
        writer.write_env("HOME", &self.home_path);
        writer.write_env("RPC_ADDR", &self.rpc_address());
        writer.write_env("GRPC_ADDR", &self.grpc_address());
    }
}

impl ChainDriver {
    /// Create a new [`ChainDriver`]
    pub fn new(
        command_path: String,
        chain_id: ChainId,
        home_path: String,
        rpc_port: u16,
        grpc_port: u16,
        p2p_port: u16,
    ) -> Self {
        Self {
            command_path,
            chain_id,
            home_path,
            rpc_port,
            grpc_port,
            p2p_port,
        }
    }

    /// Returns the full URL for the RPC address.
    pub fn rpc_address(&self) -> String {
        format!("http://localhost:{}", self.rpc_port)
    }

    /// Returns the full URL for the WebSocket address.
    pub fn websocket_address(&self) -> String {
        format!("ws://localhost:{}/websocket", self.rpc_port)
    }

    /// Returns the full URL for the GRPC address.
    pub fn grpc_address(&self) -> String {
        format!("http://localhost:{}", self.grpc_port)
    }

    /**
        Returns the full URL for the RPC address to listen to when starting
        the full node.

        This is somehow different from [`rpc_address`](ChainDriver::rpc_address)
        as it requires the `"tcp://"` scheme.
    */
    pub fn rpc_listen_address(&self) -> String {
        format!("tcp://localhost:{}", self.rpc_port)
    }

    /**
        Returns the full URL for the GRPC address to listen to when starting
        the full node.

        This is somehow different from [`grpc_address`](ChainDriver::grpc_address)
        as it requires no scheme to be specified.
    */
    pub fn grpc_listen_address(&self) -> String {
        format!("localhost:{}", self.grpc_port)
    }

    /**
       Execute the gaiad command with the given command line arguments, and
       returns the STDOUT result as String.

       This is not the most efficient way of interacting with the CLI, but
       is sufficient for testing purposes of interacting with the `gaiad`
       commmand.

       The function also output debug logs that show what command is being
       executed, so that users can manually re-run the commands by
       copying from the logs.
    */
    pub fn exec(&self, args: &[&str]) -> Result<String, Error> {
        debug!(
            "Executing command: {} {}",
            self.command_path,
            itertools::join(args, " ")
        );

        let output = Command::new(&self.command_path).args(args).output()?;

        if output.status.success() {
            let message = str::from_utf8(&output.stdout)?.to_string();
            trace!("command executed successfully with output: {}", message);

            Ok(message)
        } else {
            let message = str::from_utf8(&output.stderr)?.to_string();
            Err(eyre!(
                "command exited with error status {:?} and message: {}",
                output.status.code(),
                message
            ))
        }
    }

    /**
       Initialized the chain data stores.

       This is used by
       [`bootstrap_single_node`](crate::bootstrap::single::bootstrap_single_node).
    */
    pub fn initialize(&self) -> Result<(), Error> {
        self.exec(&[
            "--home",
            &self.home_path,
            "--chain-id",
            self.chain_id.as_str(),
            "init",
            self.chain_id.as_str(),
        ])?;

        Ok(())
    }

    /**
       Write the string content to a file path relative to the chain home
       directory.

       This is not efficient but is sufficient for testing purposes.
    */
    pub fn write_file(&self, file_path: &str, content: &str) -> Result<(), Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let full_path_str = format!("{}", full_path.display());
        fs::write(full_path, content)?;
        debug!("created new file {:?}", full_path_str);
        Ok(())
    }

    /**
       Read the content at a file path relative to the chain home
       directory, and return the result as a string.

       This is not efficient but is sufficient for testing purposes.
    */
    pub fn read_file(&self, file_path: &str) -> Result<String, Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let res = fs::read_to_string(full_path)?;
        Ok(res)
    }

    /**
       Add a wallet with random ID to the full node's keyring.
    */
    pub fn add_random_wallet(&self, prefix: &str) -> Result<Wallet, Error> {
        let num = random_u32();
        let wallet_id = format!("{}-{:x}", prefix, num);
        self.add_wallet(&wallet_id)
    }

    /**
       Add a wallet with the given ID to the full node's keyring.
    */
    pub fn add_wallet(&self, wallet_id: &str) -> Result<Wallet, Error> {
        let seed_content = self.exec(&[
            "--home",
            self.home_path.as_str(),
            "keys",
            "add",
            wallet_id,
            "--keyring-backend",
            "test",
            "--output",
            "json",
        ])?;

        let json_val: json::Value = json::from_str(&seed_content)?;
        let wallet_address = json_val
            .get("address")
            .ok_or_else(|| eyre!("expect address string field to be present in json result"))?
            .as_str()
            .ok_or_else(|| eyre!("expect address string field to be present in json result"))?
            .to_string();

        let seed_path = format!("{}-seed.json", wallet_id);
        self.write_file(&seed_path, &seed_content)?;

        let hd_path = HDPath::from_str(COSMOS_HD_PATH)
            .map_err(|e| eyre!("failed to create HDPath: {:?}", e))?;

        let key_file: KeyFile = json::from_str(&seed_content)?;

        let key = KeyEntry::from_key_file(key_file, &hd_path)?;

        Ok(Wallet::new(wallet_id.to_string(), wallet_address, key))
    }

    /**
       Add a wallet address to the genesis account list for an uninitialized
       full node.
    */
    pub fn add_genesis_account(
        &self,
        wallet: &WalletAddress,
        amounts: &[(&Denom, u64)],
    ) -> Result<(), Error> {
        let amounts_str = itertools::join(
            amounts
                .iter()
                .map(|(denom, amount)| format!("{}{}", amount, denom.0)),
            ",",
        );

        self.exec(&[
            "--home",
            &self.home_path,
            "add-genesis-account",
            &wallet.0,
            &amounts_str,
        ])?;

        Ok(())
    }

    /**
       Add a wallet ID with the given stake amount to be the genesis validator
       for an uninitialized chain.
    */
    pub fn add_genesis_validator(
        &self,
        wallet_id: &WalletId,
        denom: &Denom,
        amount: u64,
    ) -> Result<(), Error> {
        let amount_str = format!("{}{}", amount, denom.0);

        self.exec(&[
            "--home",
            &self.home_path,
            "gentx",
            &wallet_id.0,
            "--keyring-backend",
            "test",
            "--chain-id",
            self.chain_id.as_str(),
            &amount_str,
        ])?;

        Ok(())
    }

    /**
       Call `gaiad collect-gentxs` to generate the genesis transactions.
    */
    pub fn collect_gen_txs(&self) -> Result<(), Error> {
        self.exec(&["--home", &self.home_path, "collect-gentxs"])?;

        Ok(())
    }

    /**
       Modify the Gaia chain config which is saved in toml format.
    */
    pub fn update_chain_config(
        &self,
        cont: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let config1 = self.read_file("config/config.toml")?;

        let mut config2 = toml::from_str(&config1)?;

        cont(&mut config2)?;

        let config3 = toml::to_string_pretty(&config2)?;

        self.write_file("config/config.toml", &config3)?;

        Ok(())
    }

    /**
       Start a full node by running in the background `gaiad start`.

       Returns a [`ChildProcess`] that stops the full node process when the
       value is dropped.
    */
    pub fn start(&self) -> Result<ChildProcess, Error> {
        let mut child = Command::new(&self.command_path)
            .args(&[
                "--home",
                &self.home_path,
                "start",
                "--pruning",
                "nothing",
                "--grpc.address",
                &self.grpc_listen_address(),
                "--rpc.laddr",
                &self.rpc_listen_address(),
            ])
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

        pipe_to_file(stdout, &format!("{}/stdout.log", self.home_path))?;
        pipe_to_file(stderr, &format!("{}/stderr.log", self.home_path))?;

        Ok(ChildProcess::new(child))
    }

    /**
       Query for the balances for a given wallet address and denomination
    */
    pub fn query_balance(&self, wallet_id: &WalletAddress, denom: &Denom) -> Result<u64, Error> {
        let res = self.exec(&[
            "--node",
            &self.rpc_listen_address(),
            "query",
            "bank",
            "balances",
            &wallet_id.0,
            "--denom",
            denom.0.as_str(),
            "--output",
            "json",
        ])?;

        let amount_str = json::from_str::<json::Value>(&res)?
            .get("amount")
            .ok_or_else(|| eyre!("expected amount field"))?
            .as_str()
            .ok_or_else(|| eyre!("expected string field"))?
            .to_string();

        let amount = u64::from_str(&amount_str)?;

        Ok(amount)
    }

    /**
       Assert that a wallet should eventually have the expected amount in the
       given denomination.
    */
    pub fn assert_eventual_wallet_amount(
        &self,
        user: &Wallet,
        target_amount: u64,
        denom: &Denom,
    ) -> Result<(), Error> {
        assert_eventually_succeed(
            "wallet reach expected amount",
            || {
                let amount = self.query_balance(&user.address, denom)?;

                if amount == target_amount {
                    Ok(())
                } else {
                    Err(eyre!(
                        "current balance amount {} does not match the target amount {}",
                        amount,
                        target_amount
                    ))
                }
            },
            20,
            Duration::from_secs(1),
        )?;

        Ok(())
    }
}
