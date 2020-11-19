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

use ibc::ics02_client::raw::ConnectionIds as DomainTypeClientConnections;
use ibc::ics04_channel::channel::{ChannelEnd, Order, State as ChannelState};
use ibc::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::ics24_host::Path::{ChannelEnds, ClientConnections};
use relayer::chain::{Chain, CosmosSDKChain};
use relayer::config::{default, ChainConfig, Config};
use tendermint::net::Address;
use tendermint_proto::Protobuf;

use std::convert::TryInto;
use std::str::FromStr;
use tendermint::block::Height;

/// Configuration that connects to the informaldev/simd DockerHub image running on localhost.
fn simd_config() -> Config {
    let mut config = Config::default();
    config.chains = vec![ChainConfig {
        id: "ibc-test".try_into().unwrap(),
        rpc_addr: Address::from_str("127.0.0.1:26657").unwrap(),
        grpc_addr: "tcp://localhost:9090".parse().unwrap(),
        account_prefix: "cosmos".to_string(),
        key_name: "testkey".to_string(),
        store_prefix: "ibc".to_string(),
        client_ids: vec!["ethbridge".to_string()],
        gas: 200000,
        trust_threshold: Default::default(),
        trusting_period: default::trusting_period(),
        clock_drift: default::clock_drift(),
        peers: None,
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
    /* the current informaldev/simd image has an incompatible (old?) protobuf implementation
    let chain = simd_chain();
    let query = ConnectionEnd::decode_vec(
        &chain
            .abci_query(
                Connections(ConnectionId::from_str("connectionidone").unwrap()),
                0,
                false,
            )
            .unwrap(),
    );
    .unwrap();

    assert_eq!(query.state(), &ConnectionState::Init);
    assert_eq!(query.client_id(), "clientidone");
    assert_eq!(query.counterparty().client_id(), "clientidtwo");
    assert_eq!(query.counterparty().connection_id(), "connectionidtwo");
    assert_eq!(query.counterparty().prefix(), &b"prefix".to_vec().into());
    assert_eq!(
        query.versions(),
        vec!["(1,[ORDER_ORDERED,ORDER_UNORDERED])"]
    );
     */
}

/// Query channel ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_channel_id() {
    let chain = simd_chain();
    let query = ChannelEnd::decode_vec(
        &chain
            .query(
                ChannelEnds(
                    PortId::from_str("firstport").unwrap(),
                    ChannelId::from_str("firstchannel").unwrap(),
                ),
                Height::from(0_u32),
                false,
            )
            .unwrap()
            .value,
    )
    .unwrap();

    assert_eq!(query.state(), &ChannelState::Init);
    assert_eq!(query.ordering(), &Order::Ordered);
    assert_eq!(query.counterparty().port_id().as_str(), "secondport");
    assert_eq!(
        query.counterparty().channel_id().unwrap().as_str(),
        "secondchannel"
    );
    assert_eq!(query.connection_hops()[0].as_str(), "connectionidatob");
    assert_eq!(query.version(), "1.0");
}

/// Query client connections ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_client_id() {
    let chain = simd_chain();
    let query = DomainTypeClientConnections::decode_vec(
        &chain
            .query(
                ClientConnections(ClientId::from_str("clientidone").unwrap()),
                Height::from(0_u32),
                false,
            )
            .unwrap()
            .value,
    )
    .unwrap();

    assert_eq!(
        query.0[0],
        ConnectionId::from_str("connectionidone").unwrap()
    );
}
