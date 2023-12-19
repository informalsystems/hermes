use std::fs::File;
use std::io::Read;
use toml::Value;

use crate::prelude::*;

pub fn get_namada_denom_address(chain_id: &str, home_path: &str, denom: &str) -> String {
    let file_path = format!("{}/{}/wallet.toml", home_path, chain_id);
    tracing::warn!("file path: {file_path}");
    let mut toml_content = String::new();
    let mut file = File::open(file_path).expect("Failed to open file");
    file.read_to_string(&mut toml_content)
        .expect("Failed to read file");

    // Parse the TOML content into a `toml::Value` object
    let toml_value: Value = toml::from_str(&toml_content).expect("Failed to parse TOML");

    // Extract a field from the TOML file
    toml_value
        .get("addresses")
        .ok_or_else(|| eyre!("missing `addresses` field"))
        .unwrap()
        .get(denom)
        .unwrap()
        .as_str()
        .unwrap_or(denom)
        .to_owned()
}
