use std::thread::sleep;
use std::time::Duration;

use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};

use crate::ibc::denom::Denom;
use crate::prelude::*;
use crate::types::tagged::mono::Tagged;

use super::{
    itf::InformalTrace,
    state::{ChainId, DenomId, State},
};

pub const CLIENT_EXPIRY: Duration = Duration::from_secs(15);

pub fn get_chain<ChainA, ChainB, ChainX>(
    chains: &ConnectedChains<ChainA, ChainB>,
    chain_id: u64,
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
    user: u64,
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

pub fn get_port_channel_id<ChainA, ChainB, ChainX, ChainY>(
    channel: &ConnectedChannel<ChainA, ChainB>,
    chain_id: ChainId,
) -> (
    DualTagged<ChainX, ChainY, &PortId>,
    DualTagged<ChainX, ChainY, &ChannelId>,
)
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
    ChainX: ChainHandle,
    ChainY: ChainHandle,
{
    let (port_id, channel_id) = match chain_id {
        1 => {
            let port_id = channel.port_a.value();
            let channel_id = channel.channel_id_a.value();
            (port_id, channel_id)
        }
        2 => {
            let port_id = channel.port_b.value();
            let channel_id = channel.channel_id_b.value();
            (port_id, channel_id)
        }
        _ => unreachable!(),
    };
    (DualTagged::new(port_id), DualTagged::new(channel_id))
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
) -> Result<Vec<u64>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryUnreceivedPacketsRequest {
        port_id: port_id_a.to_string(),
        channel_id: channel_id_a.to_string(),
        ..Default::default()
    };
    Ok(chain.query_unreceived_packets(request)?)
}

pub fn get_committed_packets_at_src<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<PacketState>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryPacketCommitmentsRequest {
        port_id: port_id_a.to_string(),
        channel_id: channel_id_a.to_string(),
        ..Default::default()
    };
    Ok(chain.query_packet_commitments(request)?.0)
}

pub fn get_unacknowledged_packets_at_src<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<u64>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryUnreceivedAcksRequest {
        port_id: port_id_a.to_string(),
        channel_id: channel_id_a.to_string(),
        ..Default::default()
    };
    Ok(chain.query_unreceived_acknowledgement(request)?)
}

pub fn get_acknowledged_packets_at_dst<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain: &ChainA,
    channel: &ConnectedChannel<ChainA, ChainB>,
) -> Result<Vec<PacketState>, Error> {
    let port_id_a = channel.port_a.value();
    let channel_id_a = channel.channel_id_a.value();
    let request = QueryPacketAcknowledgementsRequest {
        port_id: port_id_a.to_string(),
        channel_id: channel_id_a.to_string(),
        ..Default::default()
    };
    Ok(chain.query_packet_acknowledgements(request)?.0)
}

pub fn drop<X>(_: X) {}
