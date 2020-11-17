use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyRing, KeyRingOperations};
use futures::AsyncReadExt;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

pub const KEYSTORE_HOME_FOLER: &str = ".rrly/keys/";
pub const KEYSTORE_BACKEND: &str = "keyring-test";
pub const KEYSTORE_FILE_EXTENSION: &str = "info";

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    // Get the destination chain
    let mut chain = CosmosSDKChain::from_config(opts.clone().chain_config)?;

    let keys_folder = get_keys_folder(chain.config().id.clone().as_str())
        .map_err(|e| Kind::KeyBase.context(format!("failed to create keys folder: {:?}", e)))?;

    // Create keys folder if it does not exist
    fs::create_dir_all(keys_folder.clone())
        .map_err(|e| Kind::KeyBase.context("error creating keys folder"))?;

    let key_file_contents = fs::read_to_string(&opts.file)
        .map_err(|e| Kind::KeyBase.context("error reading the key file"))?;

    // Save file to appropriate location in the keys folder
    let mut filename = Path::new(keys_folder.as_os_str()).join(chain.config().key_name.as_str());
    filename.set_extension(KEYSTORE_FILE_EXTENSION);

    let mut file =
        File::create(filename).map_err(|e| Kind::KeyBase.context("error creating the key file"))?;
    file.write_all(&key_file_contents.as_bytes())
        .map_err(|e| Kind::KeyBase.context("error writing the key file"))?;

    let key_entry = chain.keybase.key_from_seed_file(&key_file_contents);

    match key_entry {
        Ok(k) => {
            chain
                .keybase
                .add(opts.name.clone(), k.clone())
                .map_err(|e| error::Kind::KeyBase.context(e))?;
            Ok(format!(
                "Added key: {} ({})",
                opts.name.as_str(),
                k.account.as_str()
            ))
        }
        Err(e) => Err(Kind::KeyBase.context(e).into()),
    }
}

fn get_keys_folder(chain: &str) -> Result<PathBuf, Error> {
    let home = dirs::home_dir();
    match home {
        Some(h) => {
            let folder = Path::new(h.as_path())
                .join(KEYSTORE_HOME_FOLER)
                .join(chain)
                .join(KEYSTORE_BACKEND);
            Ok(folder)
        }
        None => Err(Into::<Error>::into(
            Kind::Config.context("cannot retrieve home folder"),
        )),
    }
}
