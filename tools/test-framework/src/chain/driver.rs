/*!
   Implementation of [`ChainDriver`].
*/

use core::str::FromStr;
use core::time::Duration;

use alloc::sync::Arc;
use eyre::eyre;
use serde_json as json;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::str;
use std::thread::sleep;
use tokio::runtime::Runtime;
use toml;
use tracing::debug;

use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::keyring::{HDPath, KeyEntry, KeyFile};

use crate::chain::exec::{simple_exec, ExecOutput};
use crate::error::{handle_generic_error, Error};
use crate::ibc::denom::Denom;
use crate::relayer::tx::{new_tx_config_for_test, simple_send_tx};
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::process::ChildProcess;
use crate::types::wallet::{Wallet, WalletAddress, WalletId};
use crate::util::file::pipe_to_file;
use crate::util::retry::assert_eventually_succeed;

use super::chain_type::ChainType;

pub mod interchain;
pub mod query_txs;
pub mod transfer;

/**
   Number of times (seconds) to try and query a wallet to reach the
   target amount, as used by [`assert_eventual_wallet_amount`].

   We set this to around 60 seconds to make sure that the tests still
   pass in slower environments like the CI.

   If you encounter retry error, try increasing this constant. If the
   test is taking much longer to reach eventual consistency, it might
   be indication of some underlying performance issues.
*/
const WAIT_WALLET_AMOUNT_ATTEMPTS: u16 = 90;

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
    pub chain_type: ChainType,
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

    pub account_prefix: String,

    /**
       The port used for RPC.
    */
    pub rpc_port: u16,

    /**
       The port used for GRPC.
    */
    pub grpc_port: u16,

    pub grpc_web_port: u16,

    /**
       The port used for P2P. (Currently unused other than for setup)
    */
    pub p2p_port: u16,

    pub tx_config: TxConfig,

    pub runtime: Arc<Runtime>,
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
    pub fn create(
        chain_type: ChainType,
        command_path: String,
        chain_id: ChainId,
        home_path: String,
        account_prefix: String,
        rpc_port: u16,
        grpc_port: u16,
        grpc_web_port: u16,
        p2p_port: u16,
        runtime: Arc<Runtime>,
    ) -> Result<Self, Error> {
        let tx_config = new_tx_config_for_test(
            chain_id.clone(),
            format!("http://localhost:{}", rpc_port),
            format!("http://localhost:{}", grpc_port),
            chain_type.address_type(),
        )?;

        Ok(Self {
            chain_type,
            command_path,
            chain_id,
            home_path,
            account_prefix,
            rpc_port,
            grpc_port,
            grpc_web_port,
            p2p_port,
            tx_config,
            runtime,
        })
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
    pub fn exec(&self, args: &[&str]) -> Result<ExecOutput, Error> {
        simple_exec(self.chain_id.as_str(), &self.command_path, args)
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
       Modify the Gaia genesis file.
    */
    pub fn update_genesis_file(
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
       Add a wallet with the given ID to the full node's keyring.
    */
    pub fn add_wallet(&self, wallet_id: &str) -> Result<Wallet, Error> {
        let output = self.exec(&[
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

        // gaia6 somehow displays result in stderr instead of stdout
        let seed_content = if output.stdout.is_empty() {
            output.stderr
        } else {
            output.stdout
        };

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

        let key_file: KeyFile = json::from_str(&seed_content).map_err(handle_generic_error)?;

        let key = KeyEntry::from_key_file(key_file, &hd_path).map_err(handle_generic_error)?;

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
                .map(|(denom, amount)| format!("{}{}", amount, denom)),
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
        let amount_str = format!("{}{}", amount, denom);

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

    /**
       Start a full node by running in the background `gaiad start`.

       Returns a [`ChildProcess`] that stops the full node process when the
       value is dropped.
    */
    pub fn start(&self) -> Result<ChildProcess, Error> {
        let base_args = [
            "--home",
            &self.home_path,
            "start",
            "--pruning",
            "nothing",
            "--grpc.address",
            &self.grpc_listen_address(),
            "--rpc.laddr",
            &self.rpc_listen_address(),
        ];

        let mut args: Vec<&str> = base_args.to_vec();

        let extra_start_args = self.chain_type.extra_start_args();
        args.append(&mut extra_start_args.iter().map(|s| s.as_ref()).collect());

        let mut child = Command::new(&self.command_path)
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

        let stderr_path = format!("{}/stdout.log", self.home_path);
        let stdout_path = format!("{}/stderr.log", self.home_path);

        pipe_to_file(stdout, &stderr_path)?;
        pipe_to_file(stderr, &stdout_path)?;

        // Wait for a while and check if the child process exited immediately.
        // If so, return error since we expect the full node to be running in the background.

        sleep(Duration::from_millis(1000));

        let status = child
            .try_wait()
            .map_err(|e| eyre!("error try waiting for child status: {}", e))?;

        match status {
            None => Ok(ChildProcess::new(child)),
            Some(status) => {
                let stderr_output = fs::read_to_string(stderr_path)?;
                Err(eyre!(
                    "expected full node process to be running, but it exited immediately with exit status {} and STDERR: {}",
                    status,
                    stderr_output,
                ).into())
            }
        }
    }

    /**
       Query for the balances for a given wallet address and denomination
    */
    pub fn query_balance(&self, wallet_id: &WalletAddress, denom: &Denom) -> Result<u64, Error> {
        let res = self
            .exec(&[
                "--node",
                &self.rpc_listen_address(),
                "query",
                "bank",
                "balances",
                &wallet_id.0,
                "--denom",
                denom.as_str(),
                "--output",
                "json",
            ])?
            .stdout;

        let amount_str = json::from_str::<json::Value>(&res)
            .map_err(handle_generic_error)?
            .get("amount")
            .ok_or_else(|| eyre!("expected amount field"))?
            .as_str()
            .ok_or_else(|| eyre!("expected string field"))?
            .to_string();

        let amount = u64::from_str(&amount_str).map_err(handle_generic_error)?;

        Ok(amount)
    }

    pub fn send_tx(&self, wallet: &Wallet, messages: Vec<Any>) -> Result<(), Error> {
        self.runtime
            .block_on(simple_send_tx(&self.tx_config, &wallet.key, messages))
    }

    /**
       Assert that a wallet should eventually have the expected amount in the
       given denomination.
    */
    pub fn assert_eventual_wallet_amount(
        &self,
        wallet: &WalletAddress,
        target_amount: u64,
        denom: &Denom,
    ) -> Result<(), Error> {
        assert_eventually_succeed(
            &format!("wallet reach {} amount {} {}", wallet, target_amount, denom),
            WAIT_WALLET_AMOUNT_ATTEMPTS,
            Duration::from_secs(1),
            || {
                let amount = self.query_balance(wallet, denom)?;

                if amount == target_amount {
                    Ok(())
                } else {
                    Err(Error::generic(eyre!(
                        "current balance of account {} with amount {} does not match the target amount {}",
                        wallet,
                        amount,
                        target_amount
                    )))
                }
            },
        )?;

        Ok(())
    }
}
