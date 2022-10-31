use std::thread::sleep;
use std::time::Duration;

use ibc_relayer::chain::requests::{
    QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest,
    QueryUnreceivedPacketsRequest,
};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_test_framework::ibc::denom::Denom;
use ibc_test_framework::prelude::*;
use ibc_test_framework::types::tagged::mono::Tagged;

use super::{
    itf::InformalTrace,
    state::{DenomId, State},
};

pub const CLIENT_EXPIRY: Duration = Duration::from_secs(15);

pub fn get_chain<ChainA, ChainB, ChainX>(
    chains: &ConnectedChains<ChainA, ChainB>,
    chain_id: u128,
) -> Tagged<ChainX, &FullNode>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
    ChainX: ChainHandle,
{
    Tagged::new(match chain_id {
        1 => chains.node_a.value(),
        2 => chains.node_b.value(),
        _ => unreachable!(),
    })
}

pub fn get_wallet<'a, ChainX>(
    wallets: &'a Tagged<ChainX, &TestWallets>,
    user: u128,
) -> Tagged<ChainX, &'a Wallet> {
    match user {
        1 => wallets.user1(),
        2 => wallets.user2(),
        _ => unreachable!(),
    }
}

pub fn get_denom<'a, ChainX>(
    chain: &'a Tagged<ChainX, &FullNode>,
    denom: DenomId,
) -> Tagged<ChainX, &'a Denom> {
    match denom {
        1 => chain.denom(),
        2 => chain.denom(),
        _ => unreachable!(),
    }
}

pub fn wait_for_client() {
    let sleep_time = CLIENT_EXPIRY + Duration::from_secs(5);

    info!(
        "Sleeping for {} seconds to wait for IBC client to expire",
        sleep_time.as_secs()
    );

    sleep(sleep_time);
}

pub fn parse_itf_from_json(itf_path: &str) -> Vec<State> {
    let itf_json = std::fs::read_to_string(itf_path).expect("itf file does not exist. did you run `apalache check --inv=Invariant --run-dir=run main.tla` first?");

    let trace: InformalTrace<State> =
        serde_json::from_str(&itf_json).expect("deserialization error");

    trace.states
}

pub fn get_unreceived_packets_at_dst<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<Sequence>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryUnreceivedPacketsRequest {
        port_id: port_id_a.clone(),
        channel_id: channel_id_a.clone(),
        packet_commitment_sequences: Vec::new(),
    };
    Ok(chain.query_unreceived_packets(request)?)
}

pub fn get_committed_packets_at_src<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<Sequence>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryPacketCommitmentsRequest {
        port_id: port_id_a.clone(),
        channel_id: channel_id_a.clone(),
        pagination: None,
    };
    let (sequences, _) = chain.query_packet_commitments(request)?;
    Ok(sequences)
}

pub fn get_unacknowledged_packets_at_src<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<Sequence>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryUnreceivedAcksRequest {
        port_id: port_id_a.clone(),
        channel_id: channel_id_a.clone(),
        packet_ack_sequences: Vec::new(),
    };
    Ok(chain.query_unreceived_acknowledgements(request)?)
}

pub fn get_acknowledged_packets_at_dst<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<Sequence>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryPacketAcknowledgementsRequest {
        port_id: port_id_a.clone(),
        channel_id: channel_id_a.clone(),
        pagination: None,
        packet_commitment_sequences: Vec::new(),
    };
    Ok(chain.query_packet_acknowledgements(request)?.0)
}

pub fn drop<X>(_: X) {}
