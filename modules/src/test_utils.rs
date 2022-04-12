#![allow(dead_code)]

use crate::prelude::*;
use tendermint::{block, consensus, evidence, public_key::Algorithm};

use crate::core::ics04_channel::channel::{Counterparty, Order};
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::Version;
use crate::core::ics05_port::capabilities::ChannelCapability;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::core::ics26_routing::context::{Module, ModuleOutput};
use crate::signer::Signer;

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

#[derive(Debug, Default)]
pub struct DummyModule;

impl Module for DummyModule {
    fn on_chan_open_try(
        &mut self,
        _output: &mut ModuleOutput,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _channel_cap: &ChannelCapability,
        _counterparty: &Counterparty,
        counterparty_version: &Version,
    ) -> Result<Version, Error> {
        Ok(counterparty_version.clone())
    }
}
