#![allow(dead_code, unreachable_code, unused_imports, unused_variables)]

use thiserror::Error;

use ibc::{
    ics24_host::identifier::{ChannelId, ClientId, PortId},
    Height,
};

use crate::chain::handle::ChainHandle;
use crate::chain::Chain;
use crate::channel::{Channel, ChannelError};
use crate::connection::ConnectionError;

use ibc::ics04_channel::channel::State;
use prost_types::Any;

use ibc_proto::ibc::core::channel::v1::{
    QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::foreign_client::build_update_client;

// TODO: move to config
const MAX_RETRIES: usize = 10_usize;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("Failed")]
    Failed,

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),

    #[error("ChainError:")]
    ChainError(#[from] Error),

    #[error("exhausted max number of retries:")]
    RetryError,
}

pub struct Link {
    channel: Channel,
}

impl Link {
    pub fn new(channel: Channel) -> Link {
        Link { channel }
    }

    pub fn relay(
        &self,
        _dst_chain: impl ChainHandle,
        _src_chain: impl ChainHandle,
    ) -> Result<(), LinkError> {
        // XXX: subscriptions are per channel
        // Subscriptions have to buffer events as packets can be sent before channels are
        // established
        // Can subscriptions operate as queues?
        //let subscription = src_chain.subscribe(dst_chain.id())?;

        //for (chain_id, target_height, events) in subscription.iter() {
        // let (datagrams, errors) = events
        //     .into_iter()
        //     .map(|event| src_chain.create_packet(event))
        //     .map_results(Datagram::Packet)
        //     .split_results();

        // let mut tries = 0..MAX_RETRIES;
        //
        // let result = retry(Fixed::from_millis(100), || {
        //     if let Some(attempt) = tries.next() {
        //         self.step(target_height, datagrams.clone(), signature)
        //     } else {
        //         Err(LinkError::RetryError)
        //     }
        // });

        // match result {
        //     Ok(_) => {
        //         println!("Submission successful");
        //         Ok(())
        //     }
        //     Err(problem) => {
        //         println!("Submission failed attempt with {:?}", problem);
        //         Err(LinkError::Failed)
        //     }
        // }?;
        // }

        Ok(())
    }

    // fn step(
    //     &self,
    //     target_height: Height,
    //     mut datagrams: Vec<Datagram>,
    //     signature: Signature,
    // ) -> Result<(), LinkError> {
    //     let height = self.dst_chain.query_latest_height(&self.foreign_client)?;
    //     // XXX: Check that height > target_height, no client update needed
    //     let signed_headers = self.src_chain.get_minimal_set(height, target_height)?;
    //
    //     let client_update = ClientUpdate::new(signed_headers);
    //
    //     datagrams.push(Datagram::ClientUpdate(client_update));
    //
    //     // We are missing fields here like gas and account
    //     let transaction = Transaction::new(datagrams);
    //     let signed_transaction = transaction.sign(signature);
    //     let encoded_transaction = signed_transaction.encode();
    //
    //     // Submission failure cases
    //     // - The full node can fail
    //     //  + TODO: The link will fail, and signale recreation with a different full node
    //     // - The transaction can be rejected because the client is not up to date
    //     //  + Retry this loop
    //     self.dst_chain.submit(encoded_transaction)?;
    //
    //     Ok(())
    // }
}

pub enum PacketMsgType {
    PacketRecv,
}

fn build_packet_recv_msgs(
    _dst_chain: impl ChainHandle,
    _src_chain: impl ChainHandle,
    _height: Height,
    sequences: &[u64],
) -> Result<Vec<Any>, Error> {
    let _packet_send_query =
        "send_packet.packet_src_channel=%s&send_packet.packet_sequence=%d".to_string();
    //let _events = src_chain.query_txs(height)?;
    for _seq in sequences.iter() {}
    Ok(vec![])
}

#[derive(Clone, Debug)]
pub struct PacketOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_client_id: ClientId,
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

pub fn build_packet_recv(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &PacketOptions,
) -> Result<Vec<Any>, Error> {
    let src_channel = src_chain
        .query_channel(&opts.src_port_id, &opts.src_channel_id, Height::default())
        .map_err(|e| {
            Kind::PacketRecv(
                opts.src_channel_id.clone(),
                "source channel does not exist on source".into(),
            )
            .context(e)
        })?;

    let dst_channel_id = src_channel.counterparty().channel_id.ok_or_else(|| {
        Kind::PacketRecv(
            opts.src_channel_id.clone(),
            "missing counterparty channel id".into(),
        )
    })?;

    let dst_channel = dst_chain
        .query_channel(
            &src_channel.counterparty().port_id,
            &dst_channel_id,
            Height::default(),
        )
        .map_err(|e| {
            Kind::PacketRecv(
                dst_channel_id.clone(),
                "destination channel does not exist on destination chain".into(),
            )
            .context(e)
        })?;

    if dst_channel.state().clone() != State::Open {
        return Err(Kind::PacketRecv(
            dst_channel_id,
            "channel on destination not in open state".into(),
        )
        .into());
    }

    let pc_request = QueryPacketCommitmentsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: opts.src_channel_id.to_string(),
        pagination: None,
    };

    let (packet_commitments, query_height) = src_chain.query_packet_commitments(pc_request)?;

    if packet_commitments.is_empty() {
        return Ok(vec![]);
    }

    let mut src_sequences = vec![];
    for pc in packet_commitments.iter() {
        src_sequences.append(&mut vec![pc.sequence]);
    }

    let request = QueryUnreceivedPacketsRequest {
        port_id: src_channel.counterparty().port_id.to_string(),
        channel_id: dst_channel_id.to_string(),
        packet_commitment_sequences: src_sequences,
    };

    let packets_to_send = dst_chain.query_unreceived_packets(request)?;

    println!("packets_to_send {:?}", packets_to_send);

    if packets_to_send.is_empty() {
        return Ok(vec![]);
    }

    let mut packet_msgs = build_packet_recv_msgs(
        dst_chain.clone(),
        src_chain.clone(),
        query_height,
        &packets_to_send,
    )?;

    if packet_msgs.is_empty() {
        Ok(vec![])
    } else {
        let mut msgs = build_update_client(
            dst_chain,
            src_chain,
            &opts.dst_client_id.clone(),
            query_height,
        )?;
        msgs.append(&mut packet_msgs);
        Ok(msgs)
    }
}

pub fn build_packet_recv_and_send(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &PacketOptions,
) -> Result<String, Error> {
    let dst_msgs = build_packet_recv(dst_chain.clone(), src_chain, &opts)?;
    if dst_msgs.is_empty() {
        Ok("No sent packets on source chain".to_string())
    } else {
        Ok(dst_chain.send_tx(dst_msgs)?)
    }
}
