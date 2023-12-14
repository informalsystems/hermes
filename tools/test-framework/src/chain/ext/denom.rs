use std::fs::File;
use std::io::Read;
use toml::Value;

use crate::chain::chain_type::ChainType;
use crate::ibc::denom::TaggedDenom;
use crate::prelude::*;
use crate::types::tagged::*;

pub trait ChainDenomMethodsExt<Chain> {
    fn get_denom_for_derive(&self, denom: &MonoTagged<Chain, &Denom>) -> MonoTagged<Chain, Denom>;
}

impl<'a, Chain> ChainDenomMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn get_denom_for_derive(&self, denom: &MonoTagged<Chain, &Denom>) -> TaggedDenom<Chain> {
        match self.value().chain_type {
            ChainType::Namada => {
                let file_path = format!(
                    "{}/{}/wallet.toml",
                    self.value().home_path,
                    self.value().chain_id
                );
                let mut toml_content = String::new();
                let mut file = File::open(file_path).expect("Failed to open file");
                file.read_to_string(&mut toml_content)
                    .expect("Failed to read file");

                // Parse the TOML content into a `toml::Value` object
                let toml_value: Value =
                    toml::from_str(&toml_content).expect("Failed to parse TOML");

                // Extract a field from the TOML file
                let denom_str = toml_value
                    .get("addresses")
                    .ok_or_else(|| eyre!("missing `addresses` field"))
                    .unwrap()
                    .get(denom.value().as_str())
                    .unwrap()
                    .as_str()
                    .unwrap();
                MonoTagged::new(Denom::base(denom_str))
                //MonoTagged::new(Denom::base("nam"))
            }
            _ => denom.cloned().clone(),
        }
    }
}
