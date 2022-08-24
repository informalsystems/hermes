//! Shared utilities for unit tests.

use std::fs;

use ibc::core::ics24_host::identifier::ChainId;

use crate::chain::cosmos::types::account::{Account, AccountNumber, AccountSequence};
use crate::chain::cosmos::types::config::TxConfig;
use crate::config;
use crate::keyring::{self, KeyEntry, KeyRing};

const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";

pub struct TestFixture {
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub account: Account,
}

impl TestFixture {
    pub fn new() -> Self {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );
        let config = config::load(path).expect("could not parse config");
        let chain_id = ChainId::from_string("chain_A");
        let chain_config = config.find_chain(&chain_id).unwrap();

        let tx_config = TxConfig::try_from(chain_config).expect("could not obtain tx config");

        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer-seed.json"
        );
        let seed_file_content = fs::read_to_string(path).unwrap();
        let keyring = KeyRing::new(keyring::Store::Memory, "cosmos", &chain_id).unwrap();
        let hd_path = COSMOS_HD_PATH.parse().unwrap();
        let key_entry = keyring
            .key_from_seed_file(&seed_file_content, &hd_path)
            .unwrap();

        let account = Account {
            number: AccountNumber::new(0),
            sequence: AccountSequence::new(0),
        };

        TestFixture {
            tx_config,
            key_entry,
            account,
        }
    }
}
