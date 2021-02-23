#![allow(unused_imports, unreachable_code, dead_code, unused_variables)]

use std::{collections::HashMap, thread::JoinHandle};

use abscissa_core::{Command, Options, Runnable};
use crossbeam_channel::{Receiver, Sender};
use itertools::Itertools;
use prost_types::Any;

use ibc::{
    events::IbcEvent,
    ics04_channel::{
        channel::State as ChannelState,
        events::{CloseInit, SendPacket, WriteAcknowledgement},
        msgs::recv_packet::MsgRecvPacket,
        packet::{Packet, PacketMsgType},
    },
    ics24_host::identifier::{ChainId, ChannelId, PortId},
    tx_msg::Msg,
    Height,
};
use ibc_relayer::{
    channel::Channel,
    config::Config,
    link::{Link, LinkError, LinkParameters, RelayPath},
};

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
    events: Vec<HandledEvent>,
    dst_height: Height,
}

impl WorkerCmd {
    fn new(events: Vec<HandledEvent>, dst_height: Height) -> Self {
        assert!(!events.is_empty());
        Self { events, dst_height }
    }
}

struct WorkerHandle {
    pub tx: Sender<WorkerCmd>,
    pub thread_handle: JoinHandle<()>,
}

impl WorkerHandle {
    fn handle_packet_events(
        &self,
        events: Vec<HandledEvent>,
        dst_height: Height,
    ) -> Result<(), BoxError> {
        assert!(!events.is_empty());
        self.tx.send(WorkerCmd::new(events, dst_height))?;
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
            let events_per_object = events.into_iter().group_by(|e| e.object());

            for (object, events) in events_per_object.into_iter() {
                let events: Vec<_> = events.collect();
                if events.is_empty() {
                    println!("no events in batch");
                }

                assert!(!events.is_empty());
                let worker = self.worker_for_object(object);
                worker.handle_packet_events(events, dst_height)?;
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
    rx: Receiver<WorkerCmd>,
}

impl Worker {
    fn spawn(chains: ChainHandlePair, object: Object) -> WorkerHandle {
        let (tx, rx) = crossbeam_channel::unbounded();

        let worker = Self { chains, rx };
        let thread_handle = std::thread::spawn(move || worker.run(object));

        WorkerHandle { tx, thread_handle }
    }

    fn run(self, object: Object) {
        let result = match object {
            Object::ChannelPair(channel_pair) => self.run_channel_pair(channel_pair),
        };

        if let Err(e) = result {
            eprintln!("worker error: {}", e);
        }
    }

    fn run_channel_pair(self, channel_pair: ChannelPair) -> Result<(), BoxError> {
        let link = Link::new_from_opts(
            self.chains.src.clone(),
            self.chains.dst.clone(),
            LinkParameters {
                src_port_id: channel_pair.src_port,
                src_channel_id: channel_pair.src_channel,
            },
        )?;

        while let Ok(cmd) = self.rx.recv() {
            let WorkerCmd {
                mut events,
                dst_height,
            } = cmd;

            assert!(!events.is_empty());

            let src_height =
                adjust_events_height(&self.chains, &link.a_to_b, events.as_mut_slice());
            let msgs = handle_packet_events(&self.chains, events, dst_height);

            match msgs {
                Ok(msgs) => println!("got messages after processing event: {:?}", msgs),
                Err(e) => eprintln!("error when handling packet event: {}", e),
            }
        }

        Ok(())
    }
}

fn handle_packet_events(
    chains: &ChainHandlePair,
    events: Vec<HandledEvent>,
    dst_height: Height,
) -> Result<Msgs, BoxError> {
    let mut msgs = Msgs::default();

    for event in events {
        let (dst_msg, timeout) = build_msg_from_event(&chains, &event, dst_height)?;

        if let Some(msg) = dst_msg {
            msgs.packets.push(msg);
            msgs.dst_msgs_input_events.push(event.clone());
        }

        if let Some(msg) = timeout {
            msgs.timeouts.push(msg);
            msgs.src_msgs_input_events.push(event);
        }
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

fn adjust_events_height(
    chains: &ChainHandlePair,
    relay_path: &RelayPath,
    all_events: &mut [HandledEvent],
) -> Result<Option<Height>, BoxError> {
    if all_events.is_empty() {
        return Ok(None);
    }

    // All events are at the same height
    let event_height = all_events[0].height();

    // Check if a consensus state at event_height + 1 exists on destination chain already
    // and update src_height
    if relay_path
        .dst_chain()
        .proven_client_consensus(
            relay_path.dst_client_id(),
            event_height.increment(),
            Height::zero(),
        )
        .is_ok()
    {
        return Ok(Some(event_height));
    }

    // Get the latest trusted height from the client state on destination.
    let trusted_height = relay_path
        .dst_chain()
        .query_client_state(relay_path.dst_client_id(), Height::zero())
        .map_err(|e| LinkError::QueryError(relay_path.dst_chain().id(), e))?
        .latest_height();

    // event_height + 1 is the height at which the client on destination chain
    // should be updated, unless ...
    if trusted_height > event_height.increment() {
        // ... client is already at a higher height.
        let src_height = trusted_height
            .decrement()
            .map_err(|e| LinkError::Failed(e.to_string()))?;

        println!("adjusting events height to {}", src_height);

        all_events
            .iter_mut()
            .for_each(|ev| ev.set_height(src_height));

        Ok(Some(src_height))
    } else {
        Ok(Some(event_height))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ChannelPair {
    pub src_channel: ChannelId,
    pub dst_channel: ChannelId,
    pub src_port: PortId,
    pub dst_port: PortId,
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
                src_channel: e.packet.source_channel.clone(),
                dst_channel: e.packet.destination_channel.clone(),
                src_port: e.packet.source_port.clone(),
                dst_port: e.packet.destination_port.clone(),
            }),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::SendPacket(e) => e.height(),
        }
    }

    fn set_height(&mut self, height: Height) {
        match self {
            Self::SendPacket(e) => e.set_height(height),
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
