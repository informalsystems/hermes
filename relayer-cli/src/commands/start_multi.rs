#![allow(unused_imports, unreachable_code, dead_code, unused_variables)]

use std::{collections::HashMap, sync::Arc, thread::JoinHandle};

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
            // FIXME(romac): Need to send NewBlock events to all workers
            let events = collect_events(&batch.events);
            let events_per_object = events.into_iter().group_by(ibc_event_object);

            for (object, events) in events_per_object.into_iter() {
                let events = events.collect::<Vec<_>>();
                if events.is_empty() {
                    println!("no events in batch");
                    continue;
                }

                let worker_batch = EventBatch {
                    height: batch.height,
                    chain_id: batch.chain_id.clone(),
                    events,
                };

                let worker = self.worker_for_object(object);
                worker.handle_packet_events(worker_batch)?;
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
        let mut link = Link::new_from_opts(
            self.chains.src.clone(),
            self.chains.dst.clone(),
            LinkParameters {
                src_port_id: channel_pair.src_port,
                src_channel_id: channel_pair.src_channel,
            },
        )?;

        while let Ok(cmd) = self.rx.recv() {
            link.a_to_b.relay_from_events(cmd.batch)?;
        }

        Ok(())
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

fn ibc_event_object(event: &IbcEvent) -> Object {
    match event {
        IbcEvent::SendPacket(e) => Object::ChannelPair(ChannelPair {
            src_channel: e.packet.source_channel.clone(),
            dst_channel: e.packet.destination_channel.clone(),
            src_port: e.packet.source_port.clone(),
            dst_port: e.packet.destination_port.clone(),
        }),
        _ => unreachable!(),
    }
}

fn collect_events(events: &[IbcEvent]) -> Vec<IbcEvent> {
    events
        .iter()
        .filter(|e| matches!(e, IbcEvent::SendPacket(_)))
        // IbcEvent::WriteAcknowledgement(e) => Some(HandledEvent::WriteAcknowledgement(e)),
        // IbcEvent::CloseInitChannel(e) => Some(HandledEvent::CloseInit(e)),
        .cloned()
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
