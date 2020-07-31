//! Integration test: runs the application against a live service

// Tip: Deny warnings with `RUSTFLAGS="-D warnings"` environment variable in CI

#![forbid(unsafe_code)]
#![warn(
missing_docs,
rust_2018_idioms,
trivial_casts,
unused_lifetimes,
unused_qualifications
)]

use relayer::chain::{Chain, CosmosSDKChain};
use relayer::config::{ChainConfig, Config};
use relayer_modules::ics03_connection::connection::ConnectionEnd;
use relayer_modules::ics03_connection::exported::Connection;
use relayer_modules::ics03_connection::exported::State as ConnectionState;
use relayer_modules::ics04_channel::channel::ChannelEnd;
use relayer_modules::ics04_channel::exported::Channel;
use relayer_modules::ics04_channel::exported::Order;
use relayer_modules::ics04_channel::exported::State as ChannelState;
use relayer_modules::ics23_commitment::CommitmentPrefix;
use relayer_modules::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use relayer_modules::ics24_host::Path::{ChannelEnds, ClientConnections, Connections};
use std::str::FromStr;
use tendermint::chain::Id;
use tendermint::net::Address;

/// Configuration that connects to the informaldev/simd DockerHub image running on localhost.
fn simd_config() -> Config {
    let mut config = Config::default();
    config.chains = vec![ChainConfig {
        id: Id::from("ibc-test"),
        rpc_addr: Address::from_str("127.0.0.1:26657").unwrap(),
        account_prefix: "cosmos".to_string(),
        key_name: "testkey".to_string(),
        store_prefix: "ibc".to_string(),
        client_ids: vec!["ethbridge".to_string()],
        gas: 200000,
        trusting_period: Default::default(),
    }];
    config
}

/// Chain created for the informaldev/simd DockerHub image running on localhost.
fn simd_chain() -> CosmosSDKChain {
    CosmosSDKChain::from_config(simd_config().chains[0].clone()).unwrap()
}

/// Query connection ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_connection_id() {
    let chain = simd_chain();
    let query = chain
        .query::<ConnectionEnd>(
            Connections(ConnectionId::from_str("connectionidone").unwrap()),
            0,
            false,
        )
        .unwrap();

    assert_eq!(query.state(), &ConnectionState::Init);
    assert_eq!(query.client_id(), "clientidone");
    assert_eq!(query.counterparty().client_id(), "clientidtwo");
    assert_eq!(query.counterparty().connection_id(), "connectionidtwo");
    assert_eq!(
        query.counterparty().prefix(),
        &CommitmentPrefix::new("prefix".as_bytes().to_vec())
    );
    assert_eq!(
        query.versions(),
        vec!["(1,[ORDER_ORDERED,ORDER_UNORDERED])"]
    );
}

/// Query channel ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_channel_id() {
    let chain = simd_chain();
    let query = chain
        .query::<ChannelEnd>(
            ChannelEnds(
                PortId::from_str("firstport").unwrap(),
                ChannelId::from_str("firstchannel").unwrap(),
            ),
            0,
            false,
        )
        .unwrap();

    assert_eq!(query.state(), &ChannelState::Init);
    assert_eq!(query.ordering(), &Order::Ordered);
    assert_eq!(query.counterparty().port_id(), "secondport");
    assert_eq!(query.counterparty().channel_id(), "secondchannel");
    assert_eq!(query.connection_hops()[0].as_str(), "connectionidatob");
    assert_eq!(query.version(), "1.0");
}

/// Query client connections ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_client_id() {
    let chain = simd_chain();
    let query = chain
        .query::<Vec<String>>(
            ClientConnections(ClientId::from_str("clientidone").unwrap()),
            0,
            false,
        )
        .unwrap();

    assert_eq!(query[0], "connections/connectionidone");
}
