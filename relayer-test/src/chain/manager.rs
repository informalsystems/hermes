use eyre::{eyre, Report as Error};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::str;
use tracing::{debug, trace};

use super::util;

#[derive(Debug)]
pub struct ChainManager {
    pub command_path: String,

    pub chain_id: String,

    pub home_path: String,

    pub rpc_port: u16,

    pub grpc_port: u16,
}

impl ChainManager {
    pub fn new(
        command_path: String,
        chain_id: String,
        home_path: String,
        rpc_port: u16,
        grpc_port: u16,
    ) -> Self {
        Self {
            command_path,
            chain_id,
            home_path,
            rpc_port,
            grpc_port,
        }
    }

    pub fn exec(&self, args: &[&str]) -> Result<String, Error> {
        debug!(
            "Executing command {} with arguments {:?}",
            self.command_path, args
        );

        let output = Command::new(&self.command_path)
            .args(args)
            .output()?;

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
        self.exec(&[
            "--help"
        ])?;

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

    pub fn write_file(&self, file_path: String, content: String) -> Result<(), Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let full_path_str = format!("{}", full_path.display());
        fs::write(full_path, content)?;
        debug!("created new file {:?}", full_path_str);
        Ok(())
    }

    pub fn add_random_wallet(&self, prefix: &str) -> Result<String, Error> {
        let num = util::random_u32();
        let wallet_id = format!("{}-{}", prefix, num);
        self.add_wallet(&wallet_id)?;
        Ok(wallet_id)
    }

    pub fn add_wallet(&self, wallet_id: &str) -> Result<(), Error> {
        let res = self.exec(&[
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

        let seed_path = format!("{}_seed.json", wallet_id);

        self.write_file(seed_path, res)?;

        Ok(())
    }
}
