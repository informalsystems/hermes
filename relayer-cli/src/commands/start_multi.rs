#![allow(unused_imports, unreachable_code, dead_code, unused_variables)]

use std::{collections::HashMap, thread::JoinHandle};

use abscissa_core::{Command, Options, Runnable};
use crossbeam_channel::{Receiver, Sender};
use prost_types::Any;

use ibc::{
    events::IbcEvent,
    ics04_channel::{
        channel::State as ChannelState,
        events::{CloseInit, SendPacket, WriteAcknowledgement},
        msgs::recv_packet::MsgRecvPacket,
        packet::{Packet, PacketMsgType},
    },
    ics24_host::identifier::{ChainId, ChannelId},
    tx_msg::Msg,
    Height,
};
use ibc_relayer::{config::Config, link::LinkError};

use crate::commands::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,
}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        let config = (*app_config()).clone();

        match start_multi(config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(output) => output.exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

struct WorkerCmd {
    event: HandledEvent,
    dst_height: Height,
}

struct WorkerHandle {
    pub tx: Sender<WorkerCmd>,
    pub thread_handle: JoinHandle<()>,
}

impl WorkerHandle {
    fn handle_packet_event(&self, event: HandledEvent, dst_height: Height) -> Result<(), BoxError> {
        self.tx.send(WorkerCmd { event, dst_height })?;
        Ok(())
    }
}

struct Supervisor {
    config: Config,
    chains: ChainHandlePair,
    workers: HashMap<Object, WorkerHandle>,
}

impl Supervisor {
    fn spawn(
        config: Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, BoxError> {
        let chains = ChainHandlePair::spawn(&config, src_chain_id, dst_chain_id)?;

        Ok(Self {
            config,
            chains,
            workers: HashMap::new(),
        })
    }

    fn run(&mut self) -> Result<(), BoxError> {
        let subscription = self.chains.src.subscribe()?;

        println!("iterating over event batches");

        for batch in subscription.iter() {
            let dst_height = self
                .chains
                .dst
                .query_latest_height()
                .map_err(|e| LinkError::QueryError(self.chains.dst.id(), e))?;

            let events = collect_events(&batch.events);
            for event in events {
                let object = event.object();
                let worker = self.worker_for_object(object);
                worker.handle_packet_event(event, dst_height)?;
            }
        }

        Ok(())
    }

    fn worker_for_object(&mut self, object: Object) -> &WorkerHandle {
        if self.workers.contains_key(&object) {
            &self.workers[&object]
        } else {
            let worker = Worker::spawn(self.chains.clone(), object.clone());
            self.workers.entry(object).or_insert(worker)
        }
    }
}

#[derive(Debug, Default)]
struct Msgs {
    packets: Vec<Any>,
    timeouts: Vec<Any>,
    src_msgs_input_events: Vec<HandledEvent>,
    dst_msgs_input_events: Vec<HandledEvent>,
}

struct Worker {
    chains: ChainHandlePair,
    object: Object,
    rx: Receiver<WorkerCmd>,
}

impl Worker {
    fn spawn(chains: ChainHandlePair, object: Object) -> WorkerHandle {
        let (tx, rx) = crossbeam_channel::unbounded();

        let worker = Self { chains, object, rx };
        let thread_handle = std::thread::spawn(move || worker.run());

        WorkerHandle { tx, thread_handle }
    }

    fn run(self) {
        while let Ok(cmd) = self.rx.recv() {
            let msgs = handle_packet_event(&self.chains, cmd.event, cmd.dst_height);

            match msgs {
                Ok(msgs) => {
                    println!("got messages after processing event: {:?}", msgs);
                }
                Err(e) => eprintln!(
                    "error when handling packet event for object '{:?}': {}",
                    self.object, e
                ),
            }
        }
    }
}

fn handle_packet_event(
    chains: &ChainHandlePair,
    event: HandledEvent,
    dst_height: Height,
) -> Result<Msgs, BoxError> {
    let mut msgs = Msgs::default();

    let (dst_msg, timeout) = build_msg_from_event(&chains, &event, dst_height)?;

    if let Some(msg) = dst_msg {
        msgs.packets.push(msg);
        msgs.dst_msgs_input_events.push(event.clone());
    }

    if let Some(msg) = timeout {
        msgs.timeouts.push(msg);
        msgs.src_msgs_input_events.push(event);
    }

    Ok(msgs)
}

fn build_msg_from_event(
    chains: &ChainHandlePair,
    event: &HandledEvent,
    dst_height: Height,
) -> Result<(Option<Any>, Option<Any>), BoxError> {
    match event {
        HandledEvent::SendPacket(send_packet) => {
            info!("{} => event {}", chains.src.id(), send_packet);
            build_recv_or_timeout_from_send_packet_event(chains, send_packet, dst_height)
        }
    }

    // HandledEvent::WriteAcknowledgement(write_ack_ev) => {
    //     info!("{} => event {}", chains.src.id(), write_ack_ev);
    //     Ok((Some(self.build_ack_from_recv_event(&write_ack_ev)?), None))
    // }
    // HandledEvent::CloseInit(close_init_ev) => {
    //     info!("{} => event {}", chains.src.id(), close_init_ev);
    //     Ok((
    //         Some(self.build_chan_close_confirm_from_close_init_event(&close_init_ev)?),
    //         None,
    //     ))
    // }
}

fn build_recv_or_timeout_from_send_packet_event(
    chains: &ChainHandlePair,
    event: &SendPacket,
    dst_height: Height,
) -> Result<(Option<Any>, Option<Any>), BoxError> {
    let packet = &event.packet;

    let dst_channel = chains
        .dst
        .query_channel(
            &packet.destination_port,
            &packet.destination_channel,
            dst_height,
        )
        .map_err(|e| LinkError::QueryError(chains.dst.id(), e))?;

    if dst_channel.state_matches(&ChannelState::Closed) {
        eprintln!("no support for timeout_on_close yet");
        Ok((None, None))
        // Ok((
        //     None,
        //     Some(self.build_timeout_on_close_packet(&event.packet, self.dst_height)?),
        // ))
    } else if !packet.timeout_height.is_zero() && packet.timeout_height < dst_height {
        eprintln!("no support for timeout yet");
        Ok((None, None))
        // Ok((
        //     None,
        //     Some(self.build_timeout_packet(&event.packet, self.dst_height)?),
        // ))
    } else {
        let result = build_recv_packet(chains, &event.packet, event.height)?;
        Ok((Some(result), None))
    }
}

fn build_recv_packet(
    chains: &ChainHandlePair,
    packet: &Packet,
    height: Height,
) -> Result<Any, LinkError> {
    // Get signer
    let signer = chains.dst.get_signer().map_err(|e| {
        LinkError::Failed(format!(
            "could not retrieve signer from dst chain {} with error: {}",
            chains.dst.id(),
            e
        ))
    })?;

    let (_, proofs) = chains
        .src
        .build_packet_proofs(
            PacketMsgType::Recv,
            &packet.source_port,
            &packet.source_channel,
            packet.sequence,
            height,
        )
        .map_err(|e| LinkError::PacketProofsConstructor(chains.src.id(), e))?;

    let msg = MsgRecvPacket::new(packet.clone(), proofs.clone(), signer).map_err(|e| {
        LinkError::Failed(format!(
            "error while building the recv packet for src channel {} due to error {}",
            packet.source_channel.clone(),
            e
        ))
    })?;

    info!(
        "built recv_packet msg {}, proofs at height {:?}",
        msg.packet,
        proofs.height()
    );

    use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as RawMsgRecvPacket;
    Ok(msg.to_any::<RawMsgRecvPacket>())
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ChannelPair {
    pub src: ChannelId,
    pub dst: ChannelId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Object {
    ChannelPair(ChannelPair),
}

#[derive(Clone, Debug)]
enum HandledEvent {
    SendPacket(SendPacket),
    // WriteAcknowledgement(WriteAcknowledgement),
    // CloseInit(CloseInit),
}

impl HandledEvent {
    fn object(&self) -> Object {
        match self {
            Self::SendPacket(e) => Object::ChannelPair(ChannelPair {
                src: e.packet.source_channel.clone(),
                dst: e.packet.destination_channel.clone(),
            }),
        }
    }
}

fn collect_events(events: &[IbcEvent]) -> Vec<HandledEvent> {
    events
        .iter()
        .filter_map(|e| match e {
            IbcEvent::SendPacket(e) => Some(HandledEvent::SendPacket(e.clone())),
            // IbcEvent::WriteAcknowledgement(e) => Some(HandledEvent::WriteAcknowledgement(e)),
            // IbcEvent::CloseInitChannel(e) => Some(HandledEvent::CloseInit(e)),
            _ => None,
        })
        .collect()
}

fn start_multi(
    config: Config,
    src_chain_id: &ChainId,
    dst_chain_id: &ChainId,
) -> Result<Output, BoxError> {
    let mut supervisor = Supervisor::spawn(config, src_chain_id, dst_chain_id)?;
    supervisor.run()?;

    Ok(Output::success("ok"))
}
