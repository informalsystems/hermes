use std::{
    collections::HashMap,
    thread::{self, JoinHandle},
    time::Duration,
};

use anomaly::BoxError;
use crossbeam_channel::{Receiver, Sender};

use ibc::{
    events::IbcEvent,
    ics02_client::events::NewBlock,
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::{
        channel::State as ChannelState,
        events::{CloseInit, SendPacket, TimeoutPacket, WriteAcknowledgement},
    },
    ics24_host::identifier::{ChainId, ChannelId, PortId},
    Height,
};
use tracing::info;

use crate::{
    chain::handle::ChainHandle,
    event::monitor::EventBatch,
    link::{Link, LinkParameters},
};

/// A command for a [`Worker`].
pub enum WorkerCmd {
    /// A batch of packet events need to be relayed
    PacketEvents { batch: EventBatch },
    /// A batch of [`NewBlock`] events need to be relayed
    NewBlocks {
        height: Height,
        new_blocks: Vec<NewBlock>,
    },
}

/// Handle to a [`Worker`], for sending [`WorkerCmd`]s to it.
pub struct WorkerHandle {
    tx: Sender<WorkerCmd>,
    thread_handle: JoinHandle<()>,
}

impl WorkerHandle {
    /// Send a batch of packet events to the worker.
    pub fn send_packet_events(
        &self,
        height: Height,
        events: Vec<IbcEvent>,
        chain_id: ChainId,
    ) -> Result<(), BoxError> {
        let batch = EventBatch {
            height,
            events,
            chain_id,
        };

        self.tx.send(WorkerCmd::PacketEvents { batch })?;
        Ok(())
    }

    /// Send a batch of [`NewBlock`] events to the worker.
    pub fn send_new_blocks(
        &self,
        height: Height,
        new_blocks: Vec<NewBlock>,
    ) -> Result<(), BoxError> {
        self.tx.send(WorkerCmd::NewBlocks { height, new_blocks })?;
        Ok(())
    }

    /// Wait for the worker thread to finish.
    pub fn join(self) -> thread::Result<()> {
        self.thread_handle.join()
    }
}

/// A pair of [`ChainHandle`]s.
#[derive(Clone)]
pub struct ChainHandlePair {
    pub a: Box<dyn ChainHandle>,
    pub b: Box<dyn ChainHandle>,
}

impl ChainHandlePair {
    /// Swap the two handles.
    pub fn swap(self) -> Self {
        Self {
            a: self.b,
            b: self.a,
        }
    }
}

/// The supervisor listens for events on a pair of chains,
/// and dispatches the events it receives to the appropriate
/// worker, based on the [`Object`] associated with each event.
pub struct Supervisor {
    chains: ChainHandlePair,
    workers: HashMap<Object, WorkerHandle>,
}

impl Supervisor {
    /// Spawn a supervisor which listens for events on the two given chains.
    pub fn spawn(
        chain_a: Box<dyn ChainHandle>,
        chain_b: Box<dyn ChainHandle>,
    ) -> Result<Self, BoxError> {
        let chains = ChainHandlePair {
            a: chain_a,
            b: chain_b,
        };

        Ok(Self {
            chains,
            workers: HashMap::new(),
        })
    }

    /// Run the supervisor event loop.
    pub fn run(mut self) -> Result<(), BoxError> {
        let subscription_a = self.chains.a.subscribe()?;
        let subscription_b = self.chains.b.subscribe()?;

        loop {
            for batch in subscription_a.try_iter() {
                self.process_batch(self.chains.a.clone(), batch.unwrap_or_clone())?;
            }

            for batch in subscription_b.try_iter() {
                self.process_batch(self.chains.b.clone(), batch.unwrap_or_clone())?;
            }

            std::thread::sleep(Duration::from_millis(600));
        }
    }

    /// Process a batch of events received from a chain.
    fn process_batch(
        &mut self,
        src_chain: Box<dyn ChainHandle>,
        batch: EventBatch,
    ) -> Result<(), BoxError> {
        assert_eq!(src_chain.id(), batch.chain_id);

        let height = batch.height;
        let chain_id = batch.chain_id.clone();

        let direction = if chain_id == self.chains.a.id() {
            Direction::AtoB
        } else {
            Direction::BtoA
        };

        let mut collected = collect_events(src_chain.as_ref(), batch);

        for (object, events) in collected.per_object.drain() {
            if events.is_empty() {
                continue;
            }

            println!("[{}] events: {:#?}", chain_id, events);

            if let Some(worker) = self.worker_for_object(object, direction) {
                worker.send_packet_events(height, events, chain_id.clone())?;
            }
        }

        if collected.has_new_blocks() {
            for worker in self.workers.values() {
                worker.send_new_blocks(height, collected.new_blocks.clone())?;
            }
        }

        Ok(())
    }

    /// Get a handle to the worker in charge of handling events associated
    /// with the given [`Object`].
    ///
    /// This function will spawn a new [`Worker`] if one does not exists already.
    ///
    /// The `direction` parameter indicates in which direction the worker should
    /// relay events.
    fn worker_for_object(&mut self, object: Object, direction: Direction) -> Option<&WorkerHandle> {
        if self.workers.contains_key(&object) {
            Some(&self.workers[&object])
        } else {
            let chains = match direction {
                Direction::AtoB => self.chains.clone(),
                Direction::BtoA => self.chains.clone().swap(),
            };

            if object.src_chain_id() != &chains.a.id() || object.dst_chain_id() != &chains.b.id() {
                info!(
                    "object {:?} is not relevant to worker for chains {}/{}",
                    object,
                    chains.a.id(),
                    chains.b.id()
                );

                return None;
            }

            let worker = Worker::spawn(chains, object.clone());
            let worker = self.workers.entry(object).or_insert(worker);
            Some(worker)
        }
    }
}

/// The direction in which a [`Worker`] should relay events.
#[derive(Copy, Clone, Debug)]
pub enum Direction {
    /// From chain A to chain B.
    AtoB,
    /// From chain B to chain A.
    BtoA,
}

/// A worker processes batches of events associated with a given [`Object`].
pub struct Worker {
    chains: ChainHandlePair,
    rx: Receiver<WorkerCmd>,
}

impl Worker {
    /// Spawn a worker which relay events pertaining to `object` between two `chains`.
    pub fn spawn(chains: ChainHandlePair, object: Object) -> WorkerHandle {
        let (tx, rx) = crossbeam_channel::unbounded();

        println!(
            "[{}] Spawned worker for object {:#?}",
            object.short_name(),
            object
        );

        let worker = Self { chains, rx };
        let thread_handle = std::thread::spawn(move || worker.run(object));

        WorkerHandle { tx, thread_handle }
    }

    /// Run the worker event loop.
    fn run(self, object: Object) {
        let result = match object {
            Object::UnidirectionalChannelPath(path) => self.run_uni_chan_path(path),
        };

        if let Err(e) = result {
            eprintln!("worker error: {}", e);
        }
    }

    /// Run the event loop for events associated with a [`UnidirectionalChannelPath`].
    fn run_uni_chan_path(self, path: UnidirectionalChannelPath) -> Result<(), BoxError> {
        let mut link = Link::new_from_opts(
            self.chains.a.clone(),
            self.chains.b.clone(),
            LinkParameters {
                src_port_id: path.src_port_id,
                src_channel_id: path.src_channel_id,
            },
        )?;

        while let Ok(cmd) = self.rx.recv() {
            match cmd {
                WorkerCmd::PacketEvents { batch } => link.a_to_b.update_schedule(batch)?,
                WorkerCmd::NewBlocks {
                    height,
                    new_blocks: _,
                } => link.a_to_b.clear_packets(height)?,
            }
        }

        Ok(())
    }
}

/// A unidirectional path from a source chain, channel and port.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnidirectionalChannelPath {
    /// Destination chain identifier.
    pub dst_chain_id: ChainId,

    /// Source chain identifier.
    pub src_chain_id: ChainId,

    /// Source channel identiier.
    pub src_channel_id: ChannelId,

    /// Source port identiier.
    pub src_port_id: PortId,
}

impl UnidirectionalChannelPath {
    pub fn short_name(&self) -> String {
        format!(
            "{}->{}@{}:{}",
            self.src_chain_id, self.dst_chain_id, self.src_channel_id, self.src_port_id
        )
    }
}

/// An object determines the amount of parallelism that can
/// be exercised when processing [`IbcEvent`] between
/// two chains. For each [`Object`], a corresponding
/// [`Worker`] is spawned and all [`IbcEvent`]s mapped
/// to an [`Object`] are sent to the associated [`Worker`]
/// for processing.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Object {
    /// See [`UnidirectionalChannelPath`].
    UnidirectionalChannelPath(UnidirectionalChannelPath),
}

impl From<UnidirectionalChannelPath> for Object {
    fn from(p: UnidirectionalChannelPath) -> Self {
        Self::UnidirectionalChannelPath(p)
    }
}

impl Object {
    pub fn src_chain_id(&self) -> &ChainId {
        match self {
            Self::UnidirectionalChannelPath(ref path) => &path.src_chain_id,
        }
    }

    pub fn dst_chain_id(&self) -> &ChainId {
        match self {
            Self::UnidirectionalChannelPath(ref path) => &path.dst_chain_id,
        }
    }

    pub fn short_name(&self) -> String {
        match self {
            Self::UnidirectionalChannelPath(ref path) => path.short_name(),
        }
    }

    /// Build the object associated with the given [`SendPacket`] event.
    pub fn for_send_packet(e: &SendPacket, src_chain: &dyn ChainHandle) -> Result<Self, BoxError> {
        let dst_chain_id =
            get_counterparty_chain(src_chain, &e.packet.source_channel, &e.packet.source_port)?;

        Ok(UnidirectionalChannelPath {
            dst_chain_id,
            src_chain_id: src_chain.id(),
            src_channel_id: e.packet.source_channel.clone(),
            src_port_id: e.packet.source_port.clone(),
        }
        .into())
    }

    /// Build the object associated with the given [`WriteAcknowledgement`] event.
    pub fn for_write_ack(
        e: &WriteAcknowledgement,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let dst_chain_id = get_counterparty_chain(
            src_chain,
            &e.packet.destination_channel,
            &e.packet.destination_port,
        )?;

        Ok(UnidirectionalChannelPath {
            dst_chain_id,
            src_chain_id: src_chain.id(),
            src_channel_id: e.packet.destination_channel.clone(),
            src_port_id: e.packet.destination_port.clone(),
        }
        .into())
    }

    /// Build the object associated with the given [`TimeoutPacket`] event.
    pub fn for_timeout_packet(
        e: &TimeoutPacket,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let dst_chain_id =
            get_counterparty_chain(src_chain, &e.packet.source_channel, &e.packet.source_port)?;

        Ok(UnidirectionalChannelPath {
            dst_chain_id,
            src_chain_id: src_chain.id(),
            src_channel_id: e.src_channel_id().clone(),
            src_port_id: e.src_port_id().clone(),
        }
        .into())
    }

    /// Build the object associated with the given [`CloseInit`] event.
    pub fn for_close_init_channel(
        e: &CloseInit,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let dst_chain_id = get_counterparty_chain(src_chain, e.channel_id(), &e.port_id())?;

        Ok(UnidirectionalChannelPath {
            dst_chain_id,
            src_chain_id: src_chain.id(),
            src_channel_id: e.channel_id().clone(),
            src_port_id: e.port_id().clone(),
        }
        .into())
    }
}

/// Describes the result of [`collect_events`].
#[derive(Clone, Debug)]
pub struct CollectedEvents {
    /// The height at which these events were emitted from the chain.
    pub height: Height,
    /// The chain from which the events were emitted.
    pub chain_id: ChainId,
    /// [`NewBlock`] events collected from the [`EventBatch`].
    pub new_blocks: Vec<NewBlock>,
    /// Mapping between [`Object`]s and their associated [`IbcEvent`]s.
    pub per_object: HashMap<Object, Vec<IbcEvent>>,
}

impl CollectedEvents {
    pub fn new(height: Height, chain_id: ChainId) -> Self {
        Self {
            height,
            chain_id,
            new_blocks: Default::default(),
            per_object: Default::default(),
        }
    }

    /// Whether the collected events include any [`NewBlock`] events.
    pub fn has_new_blocks(&self) -> bool {
        !self.new_blocks.is_empty()
    }
}

/// Collect the events we are interested in from an [`EventBatch`],
/// and maps each [`IbcEvent`] to their corresponding [`Object`].
pub fn collect_events(src_chain: &dyn ChainHandle, batch: EventBatch) -> CollectedEvents {
    let mut collected = CollectedEvents::new(batch.height, batch.chain_id);

    for event in batch.events {
        match event {
            IbcEvent::NewBlock(inner) => {
                collected.new_blocks.push(inner);
            }
            IbcEvent::SendPacket(ref packet) => {
                if let Ok(object) = Object::for_send_packet(packet, src_chain) {
                    collected.per_object.entry(object).or_default().push(event);
                }
            }
            IbcEvent::TimeoutPacket(ref packet) => {
                if let Ok(object) = Object::for_timeout_packet(packet, src_chain) {
                    collected.per_object.entry(object).or_default().push(event);
                }
            }
            IbcEvent::WriteAcknowledgement(ref packet) => {
                if let Ok(object) = Object::for_write_ack(packet, src_chain) {
                    collected.per_object.entry(object).or_default().push(event);
                }
            }
            IbcEvent::CloseInitChannel(ref packet) => {
                if let Ok(object) = Object::for_close_init_channel(packet, src_chain) {
                    collected.per_object.entry(object).or_default().push(event);
                }
            }
            _ => (),
        }
    }

    collected
}

// TODO: Memoize this result
fn get_counterparty_chain(
    src_chain: &dyn ChainHandle,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
) -> Result<ChainId, BoxError> {
    info!(
        chain_id = %src_chain.id(),
        src_channel_id = %src_channel_id,
        src_port_id = %src_port_id,
        "getting counterparty chain"
    );

    use ibc::ics02_client::client_state::ClientState;

    let src_channel = src_chain.query_channel(src_port_id, src_channel_id, Height::zero())?;
    if src_channel.state_matches(&ChannelState::Uninitialized) {
        return Err(format!("missing channel '{}' on source chain", src_channel_id).into());
    }

    let src_connection_id = src_channel
        .connection_hops()
        .first()
        .ok_or_else(|| format!("no connection hops for channel '{}'", src_channel_id))?;

    let src_connection = src_chain.query_connection(&src_connection_id, Height::zero())?;
    if src_connection.state_matches(&ConnectionState::Uninitialized) {
        return Err(format!("missing connection '{}' on source chain", src_connection_id).into());
    }

    let client_id = src_connection.client_id();
    let client_state = src_chain.query_client_state(client_id, Height::zero())?;

    info!(
        chain_id=%src_chain.id(), src_channel_id=%src_channel_id, src_port_id=%src_port_id,
        "counterparty chain: {}", client_state.chain_id()
    );

    Ok(client_state.chain_id())
}
