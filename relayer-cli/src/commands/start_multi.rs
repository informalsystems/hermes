#![allow(unused_imports, unreachable_code, dead_code, unused_variables)]

use std::{collections::HashMap, sync::Arc, thread::JoinHandle, time::Duration};

use abscissa_core::{Command, Options, Runnable};
use crossbeam_channel::{Receiver, Sender};
use itertools::Itertools;
use prost_types::Any;

use ibc::{
    events::IbcEvent,
    ics04_channel::{
        channel::State as ChannelState,
        events::{CloseInit, SendPacket, TimeoutPacket, WriteAcknowledgement},
        msgs::recv_packet::MsgRecvPacket,
        packet::{Packet, PacketMsgType},
    },
    ics24_host::identifier::{ChainId, ChannelId, PortId},
    tx_msg::Msg,
    Height,
};
use ibc_relayer::{
    chain::handle::ChainHandle,
    channel::Channel,
    config::Config,
    event::monitor::EventBatch,
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
    batch: Arc<EventBatch>,
}

impl WorkerCmd {
    fn new(batch: Arc<EventBatch>) -> Self {
        Self { batch }
    }
}

struct WorkerHandle {
    pub tx: Sender<WorkerCmd>,
    pub thread_handle: JoinHandle<()>,
}

impl WorkerHandle {
    fn handle_packet_events(&self, batch: EventBatch) -> Result<(), BoxError> {
        self.tx.send(WorkerCmd::new(Arc::new(batch)))?;
        Ok(())
    }
}

struct Supervisor {
    config: Config,
    chains: ChainHandlePair,
    workers: HashMap<Object, WorkerHandle>,
}

impl Supervisor {
    fn spawn(config: Config, chain_a: &ChainId, chain_b: &ChainId) -> Result<Self, BoxError> {
        let chains = ChainHandlePair::spawn(&config, chain_a, chain_b)?;

        Ok(Self {
            config,
            chains,
            workers: HashMap::new(),
        })
    }

    fn run(&mut self) -> Result<(), BoxError> {
        let subscription_a = self.chains.src.subscribe()?;
        let subscription_b = self.chains.dst.subscribe()?;

        loop {
            println!("{} => iterating over event batches", self.chains.src.id());
            for batch in subscription_a.try_iter() {
                self.process_batch(batch)?;
            }

            println!("{} => iterating over event batches", self.chains.dst.id());
            for batch in subscription_b.try_iter() {
                self.process_batch(batch)?;
            }

            std::thread::sleep(Duration::from_millis(600));
        }
    }

    fn process_batch(&mut self, batch: Arc<EventBatch>) -> Result<(), BoxError> {
        // TODO(romac): Need to send NewBlock events to all workers

        let events = collect_events(&batch.events, batch.chain_id.clone());
        let events_per_object = events.into_iter().into_group_map();

        for (object, events) in events_per_object.into_iter() {
            if events.is_empty() {
                println!("no events in batch");
                return Ok(());
            }

            let worker_batch = EventBatch {
                height: batch.height,
                chain_id: batch.chain_id.clone(),
                events,
            };

            let is_dest = batch.chain_id == self.chains.dst.id();
            let worker = self.worker_for_object(object, is_dest);
            worker.handle_packet_events(worker_batch)?;
        }

        Ok(())
    }

    fn worker_for_object(&mut self, object: Object, swap: bool) -> &WorkerHandle {
        if self.workers.contains_key(&object) {
            &self.workers[&object]
        } else {
            let chains = if swap {
                self.chains.clone().swap()
            } else {
                self.chains.clone()
            };

            let worker = Worker::spawn(chains, object.clone());
            self.workers.entry(object).or_insert(worker)
        }
    }
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
            Object::UnidirectionalChannelPath(path) => self.run_uni_chan_path(path),
        };

        if let Err(e) = result {
            eprintln!("worker error: {}", e);
        }
    }

    fn run_uni_chan_path(self, path: UnidirectionalChannelPath) -> Result<(), BoxError> {
        println!("running worker for object {:?}", path);
        let mut link = Link::new_from_opts(
            self.chains.src.clone(),
            self.chains.dst.clone(),
            LinkParameters {
                src_port_id: path.src_port_id,
                src_channel_id: path.src_channel_id,
            },
        )?;

        while let Ok(cmd) = self.rx.recv() {
            link.a_to_b.relay_from_events(cmd.batch)?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct UnidirectionalChannelPath {
    pub src_chain_id: ChainId,
    pub src_channel_id: ChannelId,
    pub src_port_id: PortId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Object {
    UnidirectionalChannelPath(UnidirectionalChannelPath),
}

impl From<UnidirectionalChannelPath> for Object {
    fn from(p: UnidirectionalChannelPath) -> Self {
        Self::UnidirectionalChannelPath(p)
    }
}

impl Object {
    fn for_send_packet(e: &SendPacket, chain_id: &ChainId) -> Self {
        UnidirectionalChannelPath {
            src_chain_id: chain_id.clone(),
            src_channel_id: e.packet.source_channel.clone(),
            src_port_id: e.packet.source_port.clone(),
        }
        .into()
    }

    fn for_write_ack(e: &WriteAcknowledgement, chain_id: &ChainId) -> Self {
        UnidirectionalChannelPath {
            src_chain_id: chain_id.clone(),
            src_channel_id: e.packet.destination_channel.clone(),
            src_port_id: e.packet.destination_port.clone(),
        }
        .into()
    }

    fn for_timeout_packet(e: &TimeoutPacket, chain_id: &ChainId) -> Self {
        UnidirectionalChannelPath {
            src_chain_id: chain_id.clone(),
            src_channel_id: e.src_channel_id().clone(),
            src_port_id: e.src_port_id().clone(),
        }
        .into()
    }

    fn for_close_init_channel(e: &CloseInit, chain_id: &ChainId) -> Self {
        UnidirectionalChannelPath {
            src_chain_id: chain_id.clone(),
            src_channel_id: e.channel_id().clone(),
            src_port_id: e.port_id().clone(),
        }
        .into()
    }
}

fn collect_events(events: &[IbcEvent], chain_id: ChainId) -> Vec<(Object, IbcEvent)> {
    events
        .iter()
        .filter_map(|e| match e {
            IbcEvent::SendPacket(p) => Some((Object::for_send_packet(p, &chain_id), e.clone())),
            IbcEvent::TimeoutPacket(p) => {
                Some((Object::for_timeout_packet(p, &chain_id), e.clone()))
            }
            IbcEvent::WriteAcknowledgement(p) => {
                Some((Object::for_write_ack(p, &chain_id), e.clone()))
            }
            IbcEvent::CloseInitChannel(p) => {
                Some((Object::for_close_init_channel(p, &chain_id), e.clone()))
            }
            _ => None,
        })
        .collect()
}

fn start_multi(config: Config, chain_a: &ChainId, chain_b: &ChainId) -> Result<Output, BoxError> {
    let mut supervisor = Supervisor::spawn(config, chain_a, chain_b)?;
    supervisor.run()?;

    Ok(Output::success("ok"))
}
