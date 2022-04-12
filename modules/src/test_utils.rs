#![allow(dead_code)]

use std::sync::{Arc, Mutex};
use tendermint::{block, consensus, evidence, public_key::Algorithm};

use crate::core::ics04_channel::channel::{Counterparty, Order};
use crate::core::ics04_channel::context::channel_capability_name;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::Version;
use crate::core::ics05_port::capabilities::Capability;
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::core::ics26_routing::context::{Module, ModuleId, ModuleOutput, RouterBuilder};
use crate::mock::context::{MockCapability, MockOCap, MockRouter, MockRouterBuilder};
use crate::prelude::*;
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

#[derive(Debug)]
pub struct DummyModule {
    ocap: Arc<Mutex<MockOCap>>,
}

impl DummyModule {
    fn new(ocap: Arc<Mutex<MockOCap>>) -> Self {
        Self { ocap }
    }
}

impl Module for DummyModule {
    fn on_chan_open_init(
        &mut self,
        _output: &mut ModuleOutput,
        _order: Order,
        _connection_hops: &[ConnectionId],
        port_id: &PortId,
        channel_id: &ChannelId,
        channel_cap: &dyn Capability,
        _counterparty: &Counterparty,
        _version: &Version,
    ) -> Result<(), Error> {
        self.ocap
            .lock()
            .unwrap()
            .claim_capability(
                dummy_module_id(),
                channel_capability_name(port_id.clone(), *channel_id),
                MockCapability::new(channel_cap.index()),
            )
            .map_err(Error::ics05_port)
    }

    fn on_chan_open_try(
        &mut self,
        _output: &mut ModuleOutput,
        _order: Order,
        _connection_hops: &[ConnectionId],
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _channel_cap: &dyn Capability,
        _counterparty: &Counterparty,
        counterparty_version: &Version,
    ) -> Result<Version, Error> {
        Ok(counterparty_version.clone())
    }
}

pub fn dummy_router(ocap: Arc<Mutex<MockOCap>>) -> MockRouter {
    MockRouterBuilder::default()
        .add_route(dummy_module_id(), DummyModule::new(ocap))
        .unwrap()
        .build()
}

pub fn dummy_module_id() -> ModuleId {
    "dummymodule".parse().unwrap()
}
