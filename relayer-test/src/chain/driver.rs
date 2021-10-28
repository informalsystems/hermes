use core::str::FromStr;
use core::time::Duration;
use eyre::{eyre, Report as Error};
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::keyring::{HDPath, KeyEntry, KeyFile};
use serde_json as json;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::str;
use toml;
use tracing::{debug, trace};

use super::wallet::{Wallet, WalletAddress, WalletId};
use crate::ibc::denom::Denom;
use crate::process::ChildProcess;
use crate::tagged::dual::Tagged;
use crate::tagged::mono::Tagged as MonoTagged;
use crate::util::file::pipe_to_file;
use crate::util::random::random_u32;
use crate::util::retry::assert_eventually_succeed;

const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";

/// The name `ChainDriver` is inspired by [WebDriver](https://developer.mozilla.org/en-US/docs/Web/WebDriver),
/// which is the term used to describe programs that control spawning of the web browsers. In our case,
/// the ChainDriver is used to spawn and manage Gaia chains.
///
/// In the future, we will want to turn this into one or more `ChainDriver` traits so that they can
/// be used to spawn multiple chain implementations other than one version of Gaia.

pub struct ChainDriver {
    pub command_path: String,

    pub chain_id: ChainId,

    pub home_path: String,

    pub rpc_port: u16,

    pub grpc_port: u16,

    pub p2p_port: u16,
}

impl ChainDriver {
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

    pub fn rpc_address(&self) -> String {
        format!("http://localhost:{}", self.rpc_port)
    }

    pub fn websocket_address(&self) -> String {
        format!("ws://localhost:{}/websocket", self.rpc_port)
    }

    pub fn grpc_address(&self) -> String {
        format!("http://localhost:{}", self.grpc_port)
    }

    pub fn rpc_listen_address(&self) -> String {
        format!("tcp://localhost:{}", self.rpc_port)
    }

    pub fn grpc_listen_address(&self) -> String {
        format!("localhost:{}", self.grpc_port)
    }

    pub fn exec(&self, args: &[&str]) -> Result<String, Error> {
        debug!(
            "Executing command {} with arguments {:?}",
            self.command_path, args
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

    pub fn help(&self) -> Result<(), Error> {
        self.exec(&["--help"])?;

        Ok(())
    }

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

    pub fn write_file(&self, file_path: &str, content: &str) -> Result<(), Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let full_path_str = format!("{}", full_path.display());
        fs::write(full_path, content)?;
        debug!("created new file {:?}", full_path_str);
        Ok(())
    }

    pub fn read_file(&self, file_path: &str) -> Result<String, Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let res = fs::read_to_string(full_path)?;
        Ok(res)
    }

    pub fn add_random_wallet(&self, prefix: &str) -> Result<Wallet, Error> {
        let num = random_u32();
        let wallet_id = format!("{}-{:x}", prefix, num);
        self.add_wallet(&wallet_id)
    }

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

    pub fn collect_gen_txs(&self) -> Result<(), Error> {
        self.exec(&["--home", &self.home_path, "collect-gentxs"])?;

        Ok(())
    }

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

    pub fn query_denom_traces(&self) -> Result<String, Error> {
        self.exec(&[
            "--node",
            &self.rpc_listen_address(),
            "query",
            "ibc-transfer",
            "denom-traces",
        ])
    }
}

impl<'a, ChainA> MonoTagged<ChainA, &'a ChainDriver> {
    // We use gaiad instead of the internal raw tx transfer to transfer tokens,
    // as the current chain implementation cannot dynamically switch the sender,
    // and instead always use the configured relayer wallet for sending tokens.
    pub fn transfer_token<ChainB>(
        &self,
        port_id: &Tagged<ChainA, ChainB, PortId>,
        channel_id: &Tagged<ChainA, ChainB, ChannelId>,
        sender: &MonoTagged<ChainA, &WalletAddress>,
        receiver: &MonoTagged<ChainB, &WalletAddress>,
        amount: u64,
        denom: &MonoTagged<ChainA, &Denom>,
    ) -> Result<(), Error> {
        self.value().exec(&[
            "--node",
            &self.value().rpc_listen_address(),
            "tx",
            "ibc-transfer",
            "transfer",
            port_id.value().as_str(),
            channel_id.value().as_str(),
            &receiver.value().0,
            &format!("{}{}", amount, denom.value().0),
            "--from",
            &sender.value().0,
            "--chain-id",
            self.value().chain_id.as_str(),
            "--home",
            &self.value().home_path,
            "--keyring-backend",
            "test",
            "--yes",
        ])?;

        Ok(())
    }

    pub fn query_balance(
        &self,
        wallet_id: &MonoTagged<ChainA, &WalletAddress>,
        denom: &MonoTagged<ChainA, &Denom>,
    ) -> Result<u64, Error> {
        let res = self.value().exec(&[
            "--node",
            &self.value().rpc_listen_address(),
            "query",
            "bank",
            "balances",
            &wallet_id.value().0,
            "--denom",
            denom.value().0.as_str(),
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

    pub fn assert_eventual_wallet_amount(
        &self,
        user: &MonoTagged<ChainA, &Wallet>,
        target_amount: u64,
        denom: &MonoTagged<ChainA, &Denom>,
    ) -> Result<(), Error> {
        assert_eventually_succeed(
            "wallet reach expected amount",
            || {
                let amount = self.query_balance(&user.address(), denom)?;

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
