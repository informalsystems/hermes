use std::{
    collections::HashMap,
    fmt,
    thread::{self, JoinHandle},
    time::Duration,
};

use anomaly::BoxError;
use crossbeam_channel::{Receiver, Select, Sender};
use itertools::Itertools;
use tracing::{debug, error, error_span, info, trace, warn};

use ibc::{
    events::{IbcEvent, VecIbcEvents},
    ics02_client::{
        client_state::ClientState,
        events::{NewBlock, UpdateClient},
    },
    ics04_channel::{
        channel::IdentifiedChannelEnd,
        events::{Attributes, CloseInit, SendPacket, TimeoutPacket, WriteAcknowledgement},
    },
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    Height,
};

use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;

use crate::channel::extract_channel_id;
use crate::channel::Channel as RelayChannel;
use crate::channel::ChannelSide;

use crate::{
    chain::{
        counterparty::{
            channel_connection_client, get_counterparty_chain, get_counterparty_chain_for_channel,
        },
        handle::ChainHandle,
    },
    config::Config,
    event::monitor::{EventBatch, UnwrapOrClone},
    foreign_client::{ForeignClient, ForeignClientError, MisbehaviourResults},
    link::{Link, LinkParameters},
    registry::Registry,
};

mod error;
pub use error::Error;

/// A command for a [`Worker`].
pub enum WorkerCmd {
    /// A batch of packet events need to be relayed
    IbcEvents { batch: EventBatch },
    /// A batch of [`NewBlock`] events need to be relayed
    NewBlock { height: Height, new_block: NewBlock },
}

/// Handle to a [`Worker`], for sending [`WorkerCmd`]s to it.
pub struct WorkerHandle {
    tx: Sender<WorkerCmd>,
    thread_handle: JoinHandle<()>,
}

impl WorkerHandle {
    /// Send a batch of packet events to the worker.
    pub fn send_events(
        &self,
        height: Height,
        events: Vec<IbcEvent>,
        chain_id: ChainId,
    ) -> Result<(), BoxError> {
        let batch = EventBatch {
            chain_id,
            height,
            events,
        };

        trace!("supervisor sends {:?}", batch);
        self.tx.send(WorkerCmd::IbcEvents { batch })?;
        Ok(())
    }

    /// Send a batch of [`NewBlock`] event to the worker.
    pub fn send_new_block(&self, height: Height, new_block: NewBlock) -> Result<(), BoxError> {
        self.tx.send(WorkerCmd::NewBlock { height, new_block })?;
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

fn recv_multiple<K, T>(rs: &[(K, Receiver<T>)]) -> Result<(&K, T), BoxError> {
    // Build a list of operations.
    let mut sel = Select::new();
    for (_, r) in rs {
        sel.recv(r);
    }

    // Complete the selected operation.
    let oper = sel.select();
    let index = oper.index();

    let (k, r) = &rs[index];

    let result = oper.recv(r)?;

    Ok((k, result))
}

/// The supervisor listens for events on multiple pairs of chains,
/// and dispatches the events it receives to the appropriate
/// worker, based on the [`Object`] associated with each event.
pub struct Supervisor {
    config: Config,
    registry: Registry,
    workers: HashMap<Object, WorkerHandle>,
}

impl Supervisor {
    /// Spawns a [`Supervisor`] which will listen for events on all the chains in the [`Config`].
    pub fn spawn(config: Config) -> Result<Self, BoxError> {
        let registry = Registry::new(config.clone());

        Ok(Self {
            config,
            registry,
            workers: HashMap::new(),
        })
    }

    /// Collect the events we are interested in from an [`EventBatch`],
    /// and maps each [`IbcEvent`] to their corresponding [`Object`].
    pub fn collect_events(
        &self,
        src_chain: &dyn ChainHandle,
        batch: EventBatch,
    ) -> CollectedEvents {
        let mut collected = CollectedEvents::new(batch.height, batch.chain_id);

        for event in batch.events {
            match event {
                IbcEvent::NewBlock(_) => {
                    collected.new_block = Some(event);
                }
                IbcEvent::UpdateClient(ref update) => {
                    if let Ok(object) = Object::for_update_client(update, src_chain) {
                        // Collect update client events only if the worker exists
                        if self.workers.get(&object).is_some() {
                            collected.per_object.entry(object).or_default().push(event);
                        }
                    }
                }

                IbcEvent::OpenInitChannel(ref open_init) => {
                    debug!("\n !!!! Init in \n ");
                    if let Ok(object) =
                        Object::for_open_init_channel(open_init.attributes(), src_chain)
                    {
                        collected.per_object.entry(object).or_default().push(event);
                    } else {
                        debug!("\n !!!! ups object malformed Init in \n ");
                    }
                }

                IbcEvent::OpenTryChannel(ref open_try) => {
                    debug!("\n !!!! OpenTry in \n ");
                    if let Ok(object) =
                        Object::for_open_try_channel(open_try.attributes(), src_chain)
                    {
                        collected.per_object.entry(object).or_default().push(event);
                    } else {
                        debug!("\n !!!! ups object malformed Try in \n ");
                    }
                }

                IbcEvent::OpenAckChannel(ref open_ack) => {
                    // Create client worker here as channel end must be opened
                    if let Ok(object) =
                        Object::for_chan_open_events(open_ack.attributes(), src_chain)
                    {
                        collected
                            .per_object
                            .entry(object)
                            .or_default()
                            .push(event.clone());
                    }

                    if let Ok(object2) =
                        Object::for_open_ack_channel(open_ack.attributes(), src_chain)
                    {
                        collected.per_object.entry(object2).or_default().push(event);
                    } else {
                        debug!("\n !!!! ups object malformed Ack in \n ");
                    }
                }
                IbcEvent::OpenConfirmChannel(ref open_confirm) => {
                    // Create client worker here as channel end must be opened
                    if let Ok(object) =
                        Object::for_chan_open_events(open_confirm.attributes(), src_chain)
                    {
                        collected
                            .per_object
                            .entry(object)
                            .or_default()
                            .push(event.clone());
                    }
                    if let Ok(object2) =
                        Object::for_open_confirm_channel(open_confirm.attributes(), src_chain)
                    {
                        collected
                            .per_object
                            .entry(object2)
                            .or_default()
                            .push(event.clone());
                    }
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

    fn spawn_workers(&mut self) {
        let req = QueryChannelsRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let chain_ids = self
            .config
            .chains
            .iter()
            .map(|c| c.id.clone())
            .collect_vec();

        for chain_id in chain_ids {
            let chain = match self.registry.get_or_spawn(&chain_id) {
                Ok(chain_handle) => chain_handle,
                Err(e) => {
                    error!("skipping workers for chain id {}. reason: failed to spawn chain runtime with error: {}", chain_id, e);
                    continue;
                }
            };

            let channels = match chain.query_channels(req.clone()) {
                Ok(channels) => channels,
                Err(e) => {
                    error!("failed to query channels from {}: {}", chain_id, e);
                    continue;
                }
            };

            for channel in channels {
                match self.spawn_workers_for_channel(chain.clone(), channel.clone()) {
                    Ok(()) => debug!(
                        "done spawning workers for channel {} on chain {}",
                        chain.id(),
                        channel.channel_id
                    ),
                    Err(e) => error!(
                        "skipped workers for channel {} on chain {} due to error {}",
                        chain.id(),
                        channel.channel_id,
                        e
                    ),
                }
            }
        }
    }

    /// Spawns all the [`Worker`]s that will handle a given channel for a given source chain.
    fn spawn_workers_for_channel(
        &mut self,
        chain: Box<dyn ChainHandle>,
        channel: IdentifiedChannelEnd,
    ) -> Result<(), BoxError> {
        trace!(
            "fetching connection_client for channel {:?} of chain {}",
            channel,
            chain.id()
        );

        let client_res =
            channel_connection_client(chain.as_ref(), &channel.port_id, &channel.channel_id);

        let (client, channel) = match client_res {
            Ok(conn_client) => (conn_client.client, conn_client.channel),
            Err(Error::ConnectionNotOpen(..)) | Err(Error::ChannelNotOpen(..)) => {
                // These errors are silent.
                // Simply ignore the channel and return without spawning the workers.
                warn!(
                    "ignoring channel {} because it is not open (or its connection is not open)",
                    channel.channel_id
                );

                return Ok(());
            }
            Err(e) => {
                // Propagate errors.
                return Err(format!(
                    "unable to spawn workers for channel/chain pair '{}'/'{}' due to error: {:?}",
                    channel.channel_id,
                    chain.id(),
                    e
                )
                .into());
            }
        };

        trace!("Obtained client id {:?}", client.client_id);

        if self
            .config
            .find_chain(&client.client_state.chain_id())
            .is_none()
        {
            // Ignore channel, since it does not correspond to any chain in the config file
            return Ok(());
        }

        if channel.channel_end.is_open() {
            //if channel open  {
            let counterparty_chain = self
                .registry
                .get_or_spawn(&client.client_state.chain_id())?;

            // create the client object and spawn worker
            let client_object = Object::Client(Client {
                dst_client_id: client.client_id.clone(),
                dst_chain_id: chain.id(),
                src_chain_id: client.client_state.chain_id(),
            });

            //if channel open
            self.worker_for_object(client_object, chain.clone(), counterparty_chain.clone());

            // TODO: Only start the Uni worker if there are outstanding packets or ACKs.
            //  https://github.com/informalsystems/ibc-rs/issues/901
            // create the path object and spawn worker
            let path_object = Object::UnidirectionalChannelPath(UnidirectionalChannelPath {
                dst_chain_id: counterparty_chain.clone().id(),
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id.clone(),
                src_port_id: channel.port_id.clone(),
            });

            self.worker_for_object(path_object, chain.clone(), counterparty_chain.clone());

            //channel object

            let counterparty_chain_id =
                get_counterparty_chain_for_channel(chain.as_ref(), channel.clone()).unwrap();

            let counterparty_chain = self.registry.get_or_spawn(&counterparty_chain_id)?;

            let channel_object = Object::Channel(Channel {
                dst_chain_id: counterparty_chain_id,
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id.clone(),
                src_port_id: channel.port_id.clone(),
                // connection_id: connection_id.clone(),
            });

            debug!(
                "create workers: creating a worker for object {:?}",
                channel_object
            );

            self.worker_for_object(channel_object, chain.clone(), counterparty_chain.clone());
        }
        // end if channel not open
        else {
            // //start spawning channel worker
            let counterparty_chain_id =
                get_counterparty_chain_for_channel(chain.as_ref(), channel.clone()).unwrap();

            let counterparty_chain = self.registry.get_or_spawn(&counterparty_chain_id)?;

            let channel_object = Object::Channel(Channel {
                dst_chain_id: counterparty_chain_id,
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id.clone(),
                src_port_id: channel.port_id.clone(),
                //connection_id: connection_id.clone(),
            });

            debug!(
                "create workers: creating a worker for object {:?}",
                channel_object
            );

            self.worker_for_object(channel_object, chain.clone(), counterparty_chain.clone());
            //end the spawning channel worker
        }

        Ok(())
    }

    /// Run the supervisor event loop.
    pub fn run(mut self) -> Result<(), BoxError> {
        let mut subscriptions = Vec::with_capacity(self.config.chains.len());

        for chain_config in &self.config.chains {
            let chain = match self.registry.get_or_spawn(&chain_config.id) {
                Ok(chain) => chain,
                Err(e) => {
                    error!(
                        "failed to spawn chain runtime for {}: {}",
                        chain_config.id, e
                    );
                    continue;
                }
            };

            match chain.subscribe() {
                Ok(subscription) => subscriptions.push((chain, subscription)),
                Err(e) => error!(
                    "failed to subscribe to events of {}: {}",
                    chain_config.id, e
                ),
            }
        }

        self.spawn_workers();

        loop {
            match recv_multiple(&subscriptions) {
                Ok((chain, batch)) => {
                    let result = batch
                        .unwrap_or_clone()
                        .map_err(Into::into)
                        .and_then(|batch| self.process_batch(chain.clone(), batch));

                    if let Err(e) = result {
                        error!("[{}] error during batch processing: {}", chain.id(), e);
                    }
                }
                Err(e) => error!("error when waiting for events: {}", e),
            }
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

        let mut collected = self.collect_events(src_chain.clone().as_ref(), batch);

        for (object, events) in collected.per_object.drain() {
            if events.is_empty() {
                continue;
            }

            debug!(
                "chain {} sent {} for object {:?}",
                chain_id,
                VecIbcEvents(events.clone()),
                object,
            );

            let src = self.registry.get_or_spawn(object.src_chain_id())?;
            let dst = self.registry.get_or_spawn(object.dst_chain_id())?;

            let worker = self.worker_for_object(object, src, dst);
            worker.send_events(height, events, chain_id.clone())?
        }

        // If there is a NewBlock event, forward the event to any workers affected by it.
        if let Some(IbcEvent::NewBlock(new_block)) = collected.new_block {
            for (_, worker) in self
                .workers
                .iter()
                .filter(|(o, _)| o.notify_new_block(&src_chain.id()))
            {
                worker.send_new_block(height, new_block)?;
            }
        }

        Ok(())
    }

    /// Get a handle to the worker in charge of handling events associated
    /// with the given [`Object`].
    ///
    /// This function will spawn a new [`Worker`] if one does not exists already.
    fn worker_for_object(
        &mut self,
        object: Object,
        src: Box<dyn ChainHandle>,
        dst: Box<dyn ChainHandle>,
    ) -> &WorkerHandle {
        if self.workers.contains_key(&object) {
            &self.workers[&object]
        } else {
            let worker = Worker::spawn(ChainHandlePair { a: src, b: dst }, object.clone());
            let worker = self.workers.entry(object).or_insert(worker);
            worker
        }
    }
}

/// A worker processes batches of events associated with a given [`Object`].
pub struct Worker {
    chains: ChainHandlePair,
    rx: Receiver<WorkerCmd>,
}

impl fmt::Display for Worker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} <-> {}]", self.chains.a.id(), self.chains.b.id(),)
    }
}

impl Worker {
    /// Spawn a worker which relay events pertaining to an [`Object`] between two `chains`.
    pub fn spawn(chains: ChainHandlePair, object: Object) -> WorkerHandle {
        let (tx, rx) = crossbeam_channel::unbounded();

        debug!(
            "[{}] spawned worker with chains a:{} and b:{} for object {:#?} ",
            object.short_name(),
            chains.a.id(),
            chains.b.id(),
            object,
        );

        let worker = Self { chains, rx };
        let thread_handle = std::thread::spawn(move || worker.run(object));

        WorkerHandle { tx, thread_handle }
    }

    /// Run the worker event loop.
    fn run(self, object: Object) {
        let span = error_span!("worker loop", worker = %object.short_name());
        let _guard = span.enter();

        let result = match object {
            Object::UnidirectionalChannelPath(path) => self.run_uni_chan_path(path),
            Object::Client(client) => self.run_client(client),
            Object::Channel(channel) => self.run_channel(channel),
        };

        if let Err(e) = result {
            error!("worker error: {}", e);
        }

        info!("worker exits");
    }

    fn run_client_misbehaviour(
        &self,
        client: &ForeignClient,
        update: Option<UpdateClient>,
    ) -> bool {
        match client.detect_misbehaviour_and_submit_evidence(update) {
            MisbehaviourResults::ValidClient => false,
            MisbehaviourResults::VerificationError => {
                // can retry in next call
                false
            }
            MisbehaviourResults::EvidenceSubmitted(_) => {
                // if evidence was submitted successfully then exit
                true
            }
            MisbehaviourResults::CannotExecute => {
                // skip misbehaviour checking if chain does not have support for it (i.e. client
                // update event does not include the header)
                true
            }
        }
    }

    /// Run the event loop for events associated with a [`Client`].
    fn run_client(self, client: Client) -> Result<(), BoxError> {
        let mut client = ForeignClient::restore(
            &client.dst_client_id,
            self.chains.a.clone(),
            self.chains.b.clone(),
        );

        info!(
            "running client worker & initial misbehaviour detection for {}",
            client
        );

        // initial check for evidence of misbehaviour for all updates
        let skip_misbehaviour = self.run_client_misbehaviour(&client, None);

        info!(
            "running client worker (misbehaviour and refresh) for {}",
            client
        );

        loop {
            thread::sleep(Duration::from_millis(600));

            // Run client refresh, exit only if expired or frozen
            if let Err(e @ ForeignClientError::ExpiredOrFrozen(..)) = client.refresh() {
                error!("failed to refresh client '{}': {}", client, e);
                continue;
            }

            if skip_misbehaviour {
                continue;
            }

            if let Ok(WorkerCmd::IbcEvents { batch }) = self.rx.try_recv() {
                trace!("client '{}' worker receives batch {:?}", client, batch);

                for event in batch.events {
                    if let IbcEvent::UpdateClient(update) = event {
                        debug!("client '{}' updated", client);

                        // Run misbehaviour. If evidence submitted the loop will exit in next
                        // iteration with frozen client
                        self.run_client_misbehaviour(&client, Some(update));
                    }
                }
            }
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

        if link.is_closed()? {
            warn!("channel is closed, exiting");
            return Ok(());
        }

        loop {
            thread::sleep(Duration::from_millis(200));

            if let Ok(cmd) = self.rx.try_recv() {
                let result = match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        // Update scheduled batches.
                        link.a_to_b.update_schedule(batch)
                    }
                    WorkerCmd::NewBlock {
                        height,
                        new_block: _,
                    } => link.a_to_b.clear_packets(height),
                };

                if let Err(e) = result {
                    error!("{}", e);
                    continue;
                }
            }

            // Refresh the scheduled batches and execute any outstanding ones.
            let result = link
                .a_to_b
                .refresh_schedule()
                .and_then(|_| link.a_to_b.execute_schedule());

            if let Err(e) = result {
                error!("{}", e);
            }
        }
    }

    /// Run the event loop for events associated with a [`Channel`].
    fn run_channel(self, channel: Channel) -> Result<(), BoxError> {
        let done = '🥳';

        let a_chain = self.chains.a.clone();
        let b_chain = self.chains.b.clone();

        // let a_channel = self.chains.a.query_channel(
        //     &channel.src_port_id,
        //     &channel.src_channel_id,
        //     Height::zero(), //height - 1 de la newBlock
        // )?;

        // let connection_id = a_channel.connection_hops().first().ok_or_else(|| {
        //     Error::MissingConnectionHops(channel.src_channel_id.clone(), a_chain.id())
        // })?;

        // let connection = self
        //     .chains
        //     .a
        //     .query_connection(&connection_id, Height::zero())?;

        // let mut state = &ibc::ics04_channel::channel::State::Uninitialized;

        // let mut b_channel = Default::default();

        // let counterparty_channel_id = if a_channel.remote.channel_id.is_none() {
        //     Default::default()
        // } else {
        //     b_channel = self.chains.b.query_channel(
        //         &a_channel.remote.port_id.clone(),
        //         &a_channel.remote.channel_id.clone().unwrap(),
        //         Height::zero(),
        //     )?;
        //     state = &b_channel.state;
        //     a_channel.remote.channel_id.clone().unwrap()
        // };

        let mut handshake_channel = RelayChannel {
            ordering: Default::default(),
            //TODO  how to get the order from raw tx
            a_side: ChannelSide::new(
                a_chain.clone(),
                Default::default(),
                Default::default(),
                Default::default(),
                Default::default(),
            ),
            b_side: ChannelSide::new(
                b_chain.clone(),
                Default::default(),
                Default::default(),
                Default::default(),
                Default::default(),
            ),
            connection_delay: Default::default(),
            //TODO  detect version from event
            version: Default::default(),
        };

        // let mut handshake_channel = RelayChannel {
        //     ordering: a_channel.ordering().clone(),
        //     a_side: ChannelSide::new(
        //         a_chain.clone(),
        //         connection.client_id().clone(),
        //         connection_id.clone(),
        //         channel.src_port_id.clone(),
        //         channel.src_channel_id.clone(),
        //     ),
        //     b_side: ChannelSide::new(
        //         b_chain.clone(),
        //         connection.counterparty().client_id().clone(),
        //         connection.counterparty().connection_id().unwrap().clone(),
        //         a_channel.remote.port_id.clone(),
        //         counterparty_channel_id.clone(),
        //     ),
        //     connection_delay: connection.delay_period(),
        //     version: Some(a_channel.version.clone()),
        // };

        // let mut stage = 0; //Nothing started
        // let mut found = false;

        // debug!(
        //     "\n [{}] initial handshake_channel is {:?}  \n ",
        //     channel.short_name(),
        //     handshake_channel
        // );

        //c0 ibc0 Init ? // -> OpenTry ibc1 -> create c1 ibc1 -->>

        //chan_open_init ibc1 => c1
        //c0 ibc0 OpenTry ? <- chan_open_try c1 ibc-1 dest c0 ibc 0 --> new channel

        // if a_channel.state_matches(&ibc::ics04_channel::channel::State::Init) {
        //     if a_channel.remote.channel_id.is_none() {
        //         let req = QueryChannelsRequest {
        //             pagination: ibc_proto::cosmos::base::query::pagination::all(),
        //         };

        //         let channels: Vec<IdentifiedChannelEnd> = b_chain.query_channels(req.clone())?;
        //         for chan in channels.iter() {
        //             if chan.channel_end.remote.channel_id.is_some()
        //                 && chan.channel_end.remote.channel_id.clone().unwrap()
        //                     == channel.src_channel_id.clone()
        //             {
        //                 debug!(
        //                     "[{}] found a pair channel {} on chain {}",
        //                     channel.short_name(),
        //                     chan.channel_id,
        //                     handshake_channel.b_side.chain_id()
        //                 );
        //                 found = true;
        //                 handshake_channel.b_side.channel_id = chan.channel_id.clone();

        //                 break;
        //             }
        //         }
        //         stage = 1; // channel in Init

        //         if !found {
        //             println!(
        //             "\n [{}] sends build_chan_open_try_and_send \n on handshake_channel {:?}  channel in state Init \n",
        //             channel.short_name(),
        //             handshake_channel
        //         );

        //             match handshake_channel.build_chan_open_try_and_send() {
        //                 Err(e) => {
        //                     debug!("Failed ChanTry {:?}: {:?}", handshake_channel.b_side, e);
        //                 }
        //                 Ok(event) => {
        //                     println!("{}  {} => {:#?}\n", done, b_chain.id(), event);
        //                 }
        //             }
        //         }
        //     }
        // } else {
        //     if a_channel.state_matches(&ibc::ics04_channel::channel::State::TryOpen) {
        //         stage = 2; //channel is in Try Open

        //         if a_channel.remote.channel_id.is_some() {
        //             //Try chanOpenTry on b_chain
        //             debug!("[{}] chain {} has channel {} in state TryOpen with counterparty {} in state {} \n", channel.short_name(), a_chain.id(), channel.src_channel_id.clone(), counterparty_channel_id.clone(), state);

        //             if !b_channel.state_matches(&ibc::ics04_channel::channel::State::Open) {
        //                 debug!(
        //                 "\n [{}] sends build_chan_open_ack_and_send \n on handshake_channel {:?}",
        //                 channel.short_name(),handshake_channel);

        //                 match handshake_channel.build_chan_open_ack_and_send() {
        //                     Err(e) => {
        //                         debug!("Failed ChanAck {:?}: {:?}", handshake_channel.b_side, e);
        //                     }
        //                     Ok(event) => {
        //                         // handshake_channel.b_side.channel_id = extract_channel_id(&event)?.clone();
        //                         println!("{}  {} => {:#?}\n", done, b_chain.id(), event);
        //                     }
        //                 }
        //             } //TODO else either counter party channel is more advanced or another channel closed the hanshake
        //         } //TODO else error
        //     } else {
        //         match (a_channel.state().clone(), state) {
        //             (
        //                 ibc::ics04_channel::channel::State::Open,
        //                 ibc::ics04_channel::channel::State::TryOpen,
        //             ) => {
        //                 stage = 3; // channel is Open
        //                 debug!(
        //                     "[{}] chain {} has channel {} in state Open counterparty TryOpen \n",
        //                     channel.short_name(),
        //                     a_chain.id(),
        //                     channel.src_channel_id.clone()
        //                 );

        //                 // Confirm to b_chain
        //                 debug!(
        //                 "[{}] sends build_chan_open_confirm_and_send \n on handshake_channel {:?}",
        //                 channel.short_name(),
        //                 handshake_channel
        //             );

        //                 match handshake_channel.build_chan_open_confirm_and_send() {
        //                     Err(e) => {
        //                         debug!(
        //                             "Failed OpenConfirm {:?}: {:?}",
        //                             handshake_channel.b_side, e
        //                         );
        //                     }
        //                     Ok(event) => {
        //                         println!("{}  {} => {:#?}\n", done, b_chain.id(), event);
        //                     }
        //                 }
        //             }
        //             (
        //                 ibc::ics04_channel::channel::State::Open,
        //                 ibc::ics04_channel::channel::State::Open,
        //             ) => {
        //                 //  stage = 3; //Channel is Open
        //                 println!(
        //                     "[{}]{}  {}  {}  Channel handshake finished for {:#?}\n",
        //                     channel.short_name(),
        //                     done,
        //                     done,
        //                     done,
        //                     &channel.src_channel_id,
        //                 );
        //                 return Ok(());
        //             }
        //             _ => {
        //                 debug!(
        //                     "[{}] \n Error Unimplemented handshake case \n",
        //                     channel.short_name()
        //                 )
        //             }
        //         }
        //     }
        // };

        let mut first_iteration = true;
        loop {
            if let Ok(cmd) = self.rx.try_recv() {
                //Ok(WorkerCmd::IbcEvents { batch })
                // Ok(cmd)
                match cmd {
                    WorkerCmd::IbcEvents { batch } => {
                        for event in batch.events {
                            match event {
                                IbcEvent::OpenInitChannel(open_init) => {
                                    debug!(
                                        "\n [{}] Calling Open Init from the loop {:?}\n ",
                                        channel.short_name(),
                                        open_init.clone()
                                    );

                                    let connection_id =
                                        open_init.attributes().connection_id.clone();
                                    let counterparty_port_id =
                                        open_init.attributes().counterparty_port_id.clone();
                                    let connection = self
                                        .chains
                                        .a
                                        .query_connection(&connection_id.clone(), Height::zero())?;
                                    let counterparty_channel_id = match open_init
                                        .attributes()
                                        .counterparty_channel_id
                                        .clone()
                                    {
                                        Some(chan_id) => chan_id,
                                        None => Default::default(),
                                    };
                                    let port_id = open_init.attributes().port_id.clone();
                                    let channel_id = match open_init.attributes().channel_id.clone()
                                    {
                                        Some(chan_id) => chan_id,
                                        None => Default::default(),
                                        //TODO err
                                    };

                                    handshake_channel = RelayChannel {
                                        ordering: Default::default(),
                                        //TODO  how to get the order from raw tx
                                        a_side: ChannelSide::new(
                                            a_chain.clone(),
                                            connection.client_id().clone(),
                                            connection_id.clone(),
                                            port_id,
                                            channel_id,
                                        ),
                                        b_side: ChannelSide::new(
                                            b_chain.clone(),
                                            connection.counterparty().client_id().clone(),
                                            connection
                                                .counterparty()
                                                .connection_id()
                                                .unwrap()
                                                .clone(),
                                            counterparty_port_id.clone(),
                                            counterparty_channel_id.clone(),
                                        ),
                                        connection_delay: connection.delay_period(),
                                        //TODO  detect version from event
                                        version: Default::default(),
                                    };

                                    debug!(
                                        "\n [{}] sends build_chan_open_try_and_send \n on handshake_channel {:?}  channel in state Init \n",
                                        channel.short_name(),
                                        handshake_channel
                                    );

                                    let connection_id =
                                        open_init.attributes().connection_id.clone();
                                    let counterparty_port_id =
                                        open_init.attributes().counterparty_port_id.clone();
                                    let connection = self
                                        .chains
                                        .a
                                        .query_connection(&connection_id.clone(), Height::zero())?;
                                    let counterparty_channel_id = match open_init
                                        .attributes()
                                        .counterparty_channel_id
                                        .clone()
                                    {
                                        Some(chan_id) => chan_id,
                                        None => Default::default(),
                                    };
                                    let port_id = open_init.attributes().port_id.clone();
                                    let channel_id = match open_init.attributes().channel_id.clone()
                                    {
                                        Some(chan_id) => chan_id,
                                        None => Default::default(),
                                        //TODO err
                                    };

                                    handshake_channel = RelayChannel {
                                        ordering: Default::default(),
                                        //TODO  how to get the order from raw tx
                                        a_side: ChannelSide::new(
                                            a_chain.clone(),
                                            connection.client_id().clone(),
                                            connection_id.clone(),
                                            port_id,
                                            channel_id,
                                        ),
                                        b_side: ChannelSide::new(
                                            b_chain.clone(),
                                            connection.counterparty().client_id().clone(),
                                            connection
                                                .counterparty()
                                                .connection_id()
                                                .unwrap()
                                                .clone(),
                                            counterparty_port_id.clone(),
                                            counterparty_channel_id.clone(),
                                        ),
                                        connection_delay: connection.delay_period(),
                                        //TODO  detect version from event
                                        version: Default::default(),
                                    };

                                    match handshake_channel.build_chan_open_try_and_send() {
                                        Err(e) => {
                                            debug!(
                                                "Failed ChanTry {:?}: {:?}",
                                                handshake_channel.b_side, e
                                            );
                                        }
                                        Ok(event) => {
                                            handshake_channel.b_side.channel_id =
                                                extract_channel_id(&event)?.clone();
                                            println!(
                                                "{}  {} => {:#?}\n",
                                                done,
                                                b_chain.id(),
                                                event.clone()
                                            );
                                        }
                                    }

                                    first_iteration = false;
                                }

                                IbcEvent::OpenTryChannel(open_try) => {
                                    debug!(
                                        "\n [{}] Calling Open Try from the loop {:?} \n ",
                                        channel.short_name(),
                                        open_try
                                    );

                                    debug!(
                                        "[{}] sends build_chan_open_ack_and_send \n on handshake_channel {:?}",
                                        channel.short_name(),
                                        handshake_channel
                                    );

                                    match handshake_channel.build_chan_open_ack_and_send() {
                                        Err(e) => {
                                            debug!(
                                                "Failed ChanAck {:?}: {:?}",
                                                handshake_channel.b_side, e
                                            );
                                        }
                                        Ok(event) => {
                                            // handshake_channel.b_side.channel_id = extract_channel_id(&event)?.clone();
                                            println!(
                                                "{}  {} => {:#?}\n",
                                                done,
                                                b_chain.id(),
                                                event
                                            );
                                        }
                                    }

                                    first_iteration = false;
                                }

                                IbcEvent::OpenAckChannel(open_ack) => {
                                    debug!(" \n [{}] channel handshake OpenAck from chain {:?} on channel {}  due to event {} \n", 
                                    channel.short_name(),
                                    handshake_channel.a_side.channel_id(),
                                    handshake_channel.a_side.chain_id(),
                                    open_ack.channel_id().clone().unwrap()
                                );

                                    //if stage == 1 && !found {
                                    // debug!(
                                    //     "[{}] writting b_side before open_confirm  ",
                                    //     channel.short_name(),
                                    //     //handshake_channel.b_side.channel_id
                                    // );

                                    // handshake_channel.b_side.channel_id =
                                    //     open_ack.counterparty_channel_id().clone().unwrap();

                                    // debug!(
                                    //     "[{}] writting b_side after open_confirm {} ",
                                    //     channel.short_name(),
                                    //     handshake_channel.b_side.channel_id
                                    // );
                                    // }

                                    // debug!(
                                    //     "[{}] hanshake_channel b_side channel id is {}",
                                    //     channel.short_name(),
                                    //     handshake_channel.b_side.channel_id()
                                    // );

                                    let event =
                                        handshake_channel.build_chan_open_confirm_and_send()?;
                                    println!("{}  {} => {:#?}\n", done, b_chain.id(), event);

                                    first_iteration = false;
                                }

                                IbcEvent::OpenConfirmChannel(open_confirm) => {
                                    debug!("[{}] {} channel handshake OpenConfirm [{}] channel from event OpenConfirm {} ", 
                                        channel.short_name(),
                                        handshake_channel.a_side.channel_id(),
                                        handshake_channel.a_side.chain_id(),
                                        open_confirm.channel_id().clone().unwrap()
                                    );

                                    println!(
                                        "{}  {}  {}  Channel handshake finished for {:#?}\n",
                                        done, done, done, &channel.src_channel_id,
                                    );

                                    // first_iteration = false;

                                    return Ok(());
                                }
                                IbcEvent::CloseInitChannel(_) => {}
                                IbcEvent::CloseConfirmChannel(_) => {}
                                _ => {}
                            }
                        }
                    }

                    WorkerCmd::NewBlock {
                        height: current_height,
                        new_block: _,
                    } => {
                        if first_iteration {
                            debug!("\n [{}] new block \n ", channel.short_name());

                            let height = current_height.decrement()?;

                            let a_channel = self.chains.a.query_channel(
                                &channel.src_port_id,
                                &channel.src_channel_id,
                                height, //current_height - 1 de la newBlock
                            )?;

                            let connection_id =
                                a_channel.connection_hops().first().ok_or_else(|| {
                                    Error::MissingConnectionHops(
                                        channel.src_channel_id.clone(),
                                        a_chain.id(),
                                    )
                                })?;

                            let connection = self
                                .chains
                                .a
                                .query_connection(&connection_id, Height::zero())?;

                            let mut counterparty_state =
                                &ibc::ics04_channel::channel::State::Uninitialized;

                            let mut b_channel = Default::default();

                            let counterparty_channel_id = if a_channel.remote.channel_id.is_none() {
                                Default::default()
                            } else {
                                b_channel = self.chains.b.query_channel(
                                    &a_channel.remote.port_id.clone(),
                                    &a_channel.remote.channel_id.clone().unwrap(),
                                    Height::zero(),
                                )?;
                                counterparty_state = &b_channel.state;
                                a_channel.remote.channel_id.clone().unwrap()
                            };

                            let mut handshake_channel = RelayChannel {
                                ordering: a_channel.ordering().clone(),
                                a_side: ChannelSide::new(
                                    a_chain.clone(),
                                    connection.client_id().clone(),
                                    connection_id.clone(),
                                    channel.src_port_id.clone(),
                                    channel.src_channel_id.clone(),
                                ),
                                b_side: ChannelSide::new(
                                    b_chain.clone(),
                                    connection.counterparty().client_id().clone(),
                                    connection.counterparty().connection_id().unwrap().clone(),
                                    a_channel.remote.port_id.clone(),
                                    counterparty_channel_id.clone(),
                                ),
                                connection_delay: connection.delay_period(),
                                version: Some(a_channel.version.clone()),
                            };

                            // let mut stage = 0; //Nothing started
                            let mut found = false;

                            debug!(
                                "\n [{}] initial handshake_channel is {:?}  \n ",
                                channel.short_name(),
                                handshake_channel
                            );

                            if a_channel.state_matches(&ibc::ics04_channel::channel::State::Init) {
                                if a_channel.remote.channel_id.is_none() {
                                    let req = QueryChannelsRequest {
                                        pagination: ibc_proto::cosmos::base::query::pagination::all(
                                        ),
                                    };
                                    //TODO Query up to a height
                                    let channels: Vec<IdentifiedChannelEnd> =
                                        b_chain.query_channels(req.clone())?;
                                    for chan in channels.iter() {
                                        if chan.channel_end.remote.channel_id.is_some()
                                            && chan.channel_end.remote.channel_id.clone().unwrap()
                                                == channel.src_channel_id.clone()
                                        {
                                            debug!(
                                                "[{}] found a pair channel {} on chain {}",
                                                channel.short_name(),
                                                chan.channel_id,
                                                handshake_channel.b_side.chain_id()
                                            );
                                            found = true;
                                            handshake_channel.b_side.channel_id =
                                                chan.channel_id.clone();

                                            break;
                                        }
                                    }
                                    // stage = 1; // channel in Init

                                    if !found {
                                        println!(
                                        "\n [{}] sends build_chan_open_try_and_send \n on handshake_channel {:?}  channel in state Init \n",
                                        channel.short_name(),
                                        handshake_channel
                                    );

                                        match handshake_channel.build_chan_open_try_and_send() {
                                            Err(e) => {
                                                debug!(
                                                    "Failed ChanTry {:?}: {:?}",
                                                    handshake_channel.b_side, e
                                                );
                                            }
                                            Ok(event) => {
                                                println!(
                                                    "{}  {} => {:#?}\n",
                                                    done,
                                                    b_chain.id(),
                                                    event
                                                );
                                            }
                                        }
                                    }
                                }
                            } else {
                                if a_channel
                                    .state_matches(&ibc::ics04_channel::channel::State::TryOpen)
                                {
                                    //stage = 2; //channel is in Try Open

                                    if a_channel.remote.channel_id.is_some() {
                                        //Try chanOpenTry on b_chain
                                        debug!("[{}] chain {} has channel {} in state TryOpen with counterparty {} in state {} \n", channel.short_name(), a_chain.id(), channel.src_channel_id.clone(), counterparty_channel_id.clone(), counterparty_state);

                                        if !b_channel.state_matches(
                                            &ibc::ics04_channel::channel::State::Open,
                                        ) {
                                            debug!(
                                            "\n [{}] sends build_chan_open_ack_and_send \n on handshake_channel {:?}",
                                            channel.short_name(),handshake_channel);

                                            match handshake_channel.build_chan_open_ack_and_send() {
                                                Err(e) => {
                                                    debug!(
                                                        "Failed ChanAck {:?}: {:?}",
                                                        handshake_channel.b_side, e
                                                    );
                                                }
                                                Ok(event) => {
                                                    // handshake_channel.b_side.channel_id = extract_channel_id(&event)?.clone();
                                                    println!(
                                                        "{}  {} => {:#?}\n",
                                                        done,
                                                        b_chain.id(),
                                                        event
                                                    );
                                                }
                                            }
                                        } //TODO else either counter party channel is more advanced or another channel closed the hanshake
                                    } //TODO else error
                                } else {
                                    match (a_channel.state().clone(), counterparty_state) {
                                        (
                                            ibc::ics04_channel::channel::State::Open,
                                            ibc::ics04_channel::channel::State::TryOpen,
                                        ) => {
                                            //stage = 3; // channel is Open
                                            debug!(
                                                "[{}] chain {} has channel {} in state Open counterparty TryOpen \n",
                                                channel.short_name(),
                                                a_chain.id(),
                                                channel.src_channel_id.clone()
                                            );

                                            // Confirm to b_chain
                                            debug!(
                                            "[{}] sends build_chan_open_confirm_and_send \n on handshake_channel {:?}",
                                            channel.short_name(),
                                            handshake_channel
                                        );

                                            match handshake_channel
                                                .build_chan_open_confirm_and_send()
                                            {
                                                Err(e) => {
                                                    debug!(
                                                        "Failed OpenConfirm {:?}: {:?}",
                                                        handshake_channel.b_side, e
                                                    );
                                                }
                                                Ok(event) => {
                                                    println!(
                                                        "{}  {} => {:#?}\n",
                                                        done,
                                                        b_chain.id(),
                                                        event
                                                    );
                                                }
                                            }
                                        }
                                        (
                                            ibc::ics04_channel::channel::State::Open,
                                            ibc::ics04_channel::channel::State::Open,
                                        ) => {
                                            //  stage = 3; //Channel is Open
                                            println!(
                                                "[{}]{}  {}  {}  Channel handshake finished for {:#?}\n",
                                                channel.short_name(),
                                                done,
                                                done,
                                                done,
                                                &channel.src_channel_id,
                                            );
                                            return Ok(());
                                        }
                                        _ => {
                                            debug!(
                                                "[{}] \n Error Unimplemented handshake case \n",
                                                channel.short_name()
                                            )
                                        }
                                    }
                                }
                            };
                        }
                    } //link.a_to_b.clear_packets(height)?,

                      // _ => {}
                }
            }
        }
    }
}

//Channel
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Channel {
    /// Destination chain identifier.
    pub dst_chain_id: ChainId,

    /// Source chain identifier.
    pub src_chain_id: ChainId,

    /// Source channel identiier.
    pub src_channel_id: ChannelId,

    /// Source port identiier.
    pub src_port_id: PortId,
    // pub connection_id: ConnectionId,
}

impl Channel {
    pub fn short_name(&self) -> String {
        format!(
            "{}/{}:{} -> {}",
            self.src_channel_id, self.src_port_id, self.src_chain_id, self.dst_chain_id,
        )
    }
}

/// Client
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Client {
    /// Destination chain identifier.
    pub dst_chain_id: ChainId,

    /// Source channel identifier.
    pub dst_client_id: ClientId,

    /// Source chain identifier.
    pub src_chain_id: ChainId,
}

impl Client {
    pub fn short_name(&self) -> String {
        format!(
            "{}->{}:{}",
            self.src_chain_id, self.dst_chain_id, self.dst_client_id
        )
    }
}

/// A unidirectional path from a source chain, channel and port.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnidirectionalChannelPath {
    /// Destination chain identifier.
    pub dst_chain_id: ChainId,

    /// Source chain identifier.
    pub src_chain_id: ChainId,

    /// Source channel identifier.
    pub src_channel_id: ChannelId,

    /// Source port identifier.
    pub src_port_id: PortId,
}

impl UnidirectionalChannelPath {
    pub fn short_name(&self) -> String {
        format!(
            "{}/{}:{}->{}",
            self.src_channel_id, self.src_port_id, self.src_chain_id, self.dst_chain_id,
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
    Channel(Channel),
    /// See [`Client`].
    Client(Client),
    /// See [`UnidirectionalChannelPath`].
    UnidirectionalChannelPath(UnidirectionalChannelPath),
}

impl Object {
    /// Returns `true` if this [`Object`] is for a [`Worker`] which is interested
    /// in new block events originating from the chain with the given [`ChainId`].
    /// Returns `false` otherwise.
    fn notify_new_block(&self, src_chain_id: &ChainId) -> bool {
        match self {
            Object::UnidirectionalChannelPath(p) => p.src_chain_id == *src_chain_id,
            Object::Client(_) => false,
            Object::Channel(_) => false,
        }
    }
}

impl From<Channel> for Object {
    fn from(c: Channel) -> Self {
        Self::Channel(c)
    }
}

impl From<Client> for Object {
    fn from(c: Client) -> Self {
        Self::Client(c)
    }
}

impl From<UnidirectionalChannelPath> for Object {
    fn from(p: UnidirectionalChannelPath) -> Self {
        Self::UnidirectionalChannelPath(p)
    }
}

impl Object {
    pub fn src_chain_id(&self) -> &ChainId {
        match self {
            Self::Channel(ref channel) => &channel.src_chain_id,
            Self::Client(ref client) => &client.src_chain_id,
            Self::UnidirectionalChannelPath(ref path) => &path.src_chain_id,
        }
    }

    pub fn dst_chain_id(&self) -> &ChainId {
        match self {
            Self::Channel(ref channel) => &channel.dst_chain_id,
            Self::Client(ref client) => &client.dst_chain_id,
            Self::UnidirectionalChannelPath(ref path) => &path.dst_chain_id,
        }
    }

    pub fn short_name(&self) -> String {
        match self {
            Self::Channel(ref channel) => channel.short_name(),
            Self::Client(ref client) => client.short_name(),
            Self::UnidirectionalChannelPath(ref path) => path.short_name(),
        }
    }

    /// Build the object associated with the given [`UpdateClient`] event.
    pub fn for_update_client(
        e: &UpdateClient,
        dst_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let client_state = dst_chain.query_client_state(e.client_id(), Height::zero())?;
        if client_state.refresh_period().is_none() {
            return Err(format!(
                "client '{}' on chain {} does not require refresh",
                e.client_id(),
                dst_chain.id()
            )
            .into());
        }

        let src_chain_id = client_state.chain_id();

        Ok(Client {
            dst_client_id: e.client_id().clone(),
            dst_chain_id: dst_chain.id(),
            src_chain_id,
        }
        .into())
    }

    /// Build the object associated with the given [`OpenInit`] event.
    pub fn for_open_init_channel(
        e: &Attributes,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let channel_id = e
            .channel_id()
            .as_ref()
            .ok_or_else(|| format!("channel_id missing in OpenInit event '{:?}'", e))?;

        let dst_chain_id = get_counterparty_chain(src_chain, channel_id, &e.port_id());

        if dst_chain_id.is_err() {
            debug!("\n err dest_chan_id in init\n ");
            return Err(format!("dest chain missing in init").into());
        }

        debug!(
            " in for_open_init_channel dst_chain_id {} src_chain_id {} with event {:?} ",
            dst_chain_id.clone().unwrap(),
            src_chain.id(),
            e
        );

        Ok(Channel {
            dst_chain_id: dst_chain_id.clone().unwrap(),
            src_chain_id: src_chain.id(),
            src_channel_id: channel_id.clone(),
            src_port_id: e.port_id().clone(),
            //connection_id: e.connection_id().clone(),
        }
        .into())
    }

    /// Build the object associated with the given [`OpenTry`] event.
    pub fn for_open_try_channel(
        e: &Attributes,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let channel_id = e
            .channel_id()
            .as_ref()
            .ok_or_else(|| format!("channel_id missing in OpenInit event '{:?}'", e))?;

        let dst_chain_id = get_counterparty_chain(src_chain, channel_id, &e.port_id());

        if dst_chain_id.is_err() {
            debug!("\n err dest_chan_id in try\n ");
            return Err(format!("dest chain missing in OpenTry").into());
        }

        debug!(
            " in for_open_try_channel dst_chain_id {} src_chain_id {} with event {:?} ",
            dst_chain_id.clone().unwrap(),
            src_chain.id(),
            e
        );

        Ok(Channel {
            dst_chain_id: dst_chain_id.clone().unwrap(),
            src_chain_id: src_chain.id(),
            src_channel_id: e.channel_id().clone().unwrap(),
            src_port_id: e.port_id().clone(),
        }
        .into())
    }

    pub fn for_open_ack_channel(
        e: &Attributes,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let dst_chain_id =
            get_counterparty_chain(src_chain, &e.channel_id().clone().unwrap(), &e.port_id())?;

        debug!(
            " in for_open_ack_channel dst_chain_id {} src_chain_id {} with event {:?} ",
            dst_chain_id,
            src_chain.id(),
            e
        );

        Ok(Channel {
            dst_chain_id,
            src_chain_id: src_chain.id(),
            src_channel_id: e.channel_id().clone().unwrap(),
            src_port_id: e.port_id().clone(),
            // connection_id: e.connection_id().clone(),
        }
        .into())
    }

    pub fn for_open_confirm_channel(
        e: &Attributes,
        src_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let dst_chain_id =
            get_counterparty_chain(src_chain, &e.channel_id().clone().unwrap(), &e.port_id())?;

        debug!(
            " in for_open_confirm_channel dst_chain_id {} src_chain_id {} with event {:?} ",
            dst_chain_id,
            src_chain.id(),
            e
        );

        Ok(Channel {
            dst_chain_id,
            src_chain_id: src_chain.id(),
            src_channel_id: e.channel_id().clone().unwrap(),
            src_port_id: e.port_id().clone(),
            // connection_id: e.connection_id().clone(),
        }
        .into())
    }

    /// Build the client object associated with the given channel event attributes.
    pub fn for_chan_open_events(
        e: &Attributes,
        dst_chain: &dyn ChainHandle,
    ) -> Result<Self, BoxError> {
        let channel_id = e
            .channel_id()
            .as_ref()
            .ok_or_else(|| format!("channel_id missing in OpenAck event '{:?}'", e))?;

        let client = channel_connection_client(dst_chain, e.port_id(), channel_id)?.client;
        if client.client_state.refresh_period().is_none() {
            return Err(format!(
                "client '{}' on chain {} does not require refresh",
                client.client_id,
                dst_chain.id()
            )
            .into());
        }

        Ok(Client {
            dst_client_id: client.client_id.clone(),
            dst_chain_id: dst_chain.id(),
            src_chain_id: client.client_state.chain_id(),
        }
        .into())
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
    /// [`NewBlock`] event collected from the [`EventBatch`].
    pub new_block: Option<IbcEvent>,
    /// Mapping between [`Object`]s and their associated [`IbcEvent`]s.
    pub per_object: HashMap<Object, Vec<IbcEvent>>,
}

impl CollectedEvents {
    pub fn new(height: Height, chain_id: ChainId) -> Self {
        Self {
            height,
            chain_id,
            new_block: Default::default(),
            per_object: Default::default(),
        }
    }

    /// Whether the collected events include a [`NewBlock`] event.
    pub fn has_new_block(&self) -> bool {
        self.new_block.is_some()
    }
}
