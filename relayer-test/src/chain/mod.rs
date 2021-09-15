use eyre::{eyre, Report as Error};
use ibc::ics24_host::identifier::ChainId;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::str;
use tracing::debug;

pub struct ChainManager {
    command_path: String,

    chain_id: ChainId,

    home_path: String,

    keyring_backend: String,

    rpc_port: u16,

    grpc_port: u16,
}

pub struct ChainGenerator {
    command_path: String,

    store_path: String,

    next_chain_id: u64,

    next_rpc_port: u16,

    next_grpc_port: u16,
}

impl ChainManager {
    fn exec(&self, args: &[&str]) -> Result<String, Error> {
        debug!(
            "Executing command {} with arguments {:?}",
            self.command_path, args
        );

        let output = Command::new(&self.command_path)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .output()?;

        if output.status.success() {
            Ok(str::from_utf8(&output.stdout)?.to_string())
        } else {
            Err(eyre!(
                "command exited with error status {:?}",
                output.status.code()
            ))
        }
    }

    fn initialize(&self) -> Result<(), Error> {
        self.exec(&[
            "--home",
            &self.home_path.as_str(),
            "--chain-id",
            self.chain_id.as_str(),
            "init",
            self.chain_id.as_str(),
        ])?;

        Ok(())
    }

    fn write_file(&self, file_path: &Path, content: String) -> Result<(), Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        fs::write(full_path, content)?;
        Ok(())
    }

    fn add_validator(&self) -> Result<(), Error> {
        let output = self.exec(&[
            "--home",
            self.home_path.as_str(),
            "keys",
            "add",
            "validator",
            "--keyring-backend",
            &self.keyring_backend,
            "--output",
            "json",
        ])?;

        Ok(())
    }
}
