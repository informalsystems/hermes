use std::sync::{Arc, Mutex};
use std::time::Duration;

use crate::clients::host_functions::HostFunctionsProvider;
use crate::prelude::*;
use sp_core::keccak_256;
use sp_trie::LayoutV0;
use tendermint::{block, consensus, evidence, public_key::Algorithm};

use crate::clients::ics11_beefy::error::Error as BeefyError;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics04_channel::channel::{Counterparty, Order};
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::packet::{Receipt, Sequence};
use crate::core::ics04_channel::Version;
use crate::core::ics05_port::context::PortReader;
use crate::core::ics05_port::error::Error as PortError;
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::core::ics26_routing::context::{Module, ModuleId, ModuleOutputBuilder};
use crate::mock::context::MockIbcStore;
use crate::prelude::*;
use crate::signer::Signer;
use crate::timestamp::Timestamp;
use crate::Height;

// Needed in mocks.
pub fn default_consensus_params() -> consensus::Params {
    consensus::Params {
        block: block::Size {
            max_bytes: 22020096,
            max_gas: -1,
            time_iota_ms: 1000,
        },
        evidence: evidence::Params {
            max_age_num_blocks: 100000,
            max_age_duration: evidence::Duration(core::time::Duration::new(48 * 3600, 0)),
            max_bytes: 0,
        },
        validator: consensus::params::ValidatorParams {
            pub_key_types: vec![Algorithm::Ed25519],
        },
        version: Some(consensus::params::VersionParams::default()),
    }
}

pub fn get_dummy_proof() -> Vec<u8> {
    "Y29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIy"
        .as_bytes()
        .to_vec()
}

pub fn get_dummy_account_id() -> Signer {
    "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C".parse().unwrap()
}

pub fn get_dummy_bech32_account() -> String {
    "cosmos1wxeyh7zgn4tctjzs0vtqpc6p5cxq5t2muzl7ng".to_string()
}

#[derive(Debug)]
pub struct DummyTransferModule {
    ibc_store: Arc<Mutex<MockIbcStore>>,
}

impl DummyTransferModule {
    pub fn new(ibc_store: Arc<Mutex<MockIbcStore>>) -> Self {
        Self { ibc_store }
    }
}

impl Module for DummyTransferModule {
    fn on_chan_open_try(
        &mut self,
        _output: &mut ModuleOutputBuilder,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _counterparty: &Counterparty,
        _version: &Version,
        counterparty_version: &Version,
    ) -> Result<Version, Error> {
        Ok(counterparty_version.clone())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Crypto;

impl HostFunctionsProvider for Crypto {
    fn keccak_256(input: &[u8]) -> [u8; 32] {
        keccak_256(input)
    }

    fn secp256k1_ecdsa_recover_compressed(
        signature: &[u8; 65],
        value: &[u8; 32],
    ) -> Option<Vec<u8>> {
        sp_io::crypto::secp256k1_ecdsa_recover_compressed(signature, value)
            .ok()
            .map(|val| val.to_vec())
    }

    fn ed25519_recover(_signature: &[u8; 64], _value: &[u8; 32]) -> Option<Vec<u8>> {
        todo!()
    }

    fn verify_membership_trie_proof(
        root: &sp_core::H256,
        proof: &[Vec<u8>],
        key: &[u8],
        value: &[u8],
    ) -> Result<(), Ics02Error> {
        let item = vec![(key, Some(value))];
        sp_trie::verify_trie_proof::<LayoutV0<sp_runtime::traits::BlakeTwo256>, _, _, _>(
            root, proof, &item,
        )
        .map_err(|_| Ics02Error::beefy(BeefyError::invalid_trie_proof()))
    }

    fn verify_non_membership_trie_proof(
        root: &sp_core::H256,
        proof: &[Vec<u8>],
        key: &[u8],
    ) -> Result<(), Ics02Error> {
        let item: Vec<(&[u8], Option<&[u8]>)> = vec![(key, None)];
        sp_trie::verify_trie_proof::<LayoutV0<sp_runtime::traits::BlakeTwo256>, _, _, _>(
            root, proof, &item,
        )
        .map_err(|_| Ics02Error::beefy(BeefyError::invalid_trie_proof()))
    }

    fn sha256_digest(data: &[u8]) -> [u8; 32] {
        sp_io::hashing::sha2_256(data)
    }
}
