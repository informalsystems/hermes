use std::{collections::HashMap, sync::Arc, time::Duration};

use anomaly::BoxError;

use crossbeam_channel::{Receiver, Sender};
use itertools::Itertools;
use tracing::{debug, error, trace, warn};

use ibc::{
    events::IbcEvent, ics02_client::client_state::ClientState,
    ics04_channel::channel::IdentifiedChannelEnd, ics24_host::identifier::ChainId, Height,
};

use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;

use crate::{
    chain::{
        counterparty::{channel_connection_client, get_counterparty_chain_for_channel},
        handle::{ChainHandle, ChainHandlePair},
    },
    config::Config,
    event::{
        self,
        monitor::{EventBatch, UnwrapOrClone},
    },
    object::{Channel, Client, Object, UnidirectionalChannelPath},
    registry::Registry,
    util::try_recv_multiple,
    worker::{Worker, WorkerHandle, WorkerMsg},
};

pub mod error;
pub use error::Error;

/// The supervisor listens for events on multiple pairs of chains,
/// and dispatches the events it receives to the appropriate
/// worker, based on the [`Object`] associated with each event.
pub struct Supervisor {
    config: Config,
    registry: Registry,
    workers: HashMap<Object, WorkerHandle>,
    worker_msg_tx: Sender<WorkerMsg>,
    worker_msg_rx: Receiver<WorkerMsg>,
}

impl Supervisor {
    /// Spawns a [`Supervisor`] which will listen for events on all the chains in the [`Config`].
    pub fn spawn(config: Config) -> Result<Self, BoxError> {
        let registry = Registry::new(config.clone());
        let (worker_msg_tx, worker_msg_rx) = crossbeam_channel::unbounded();

        Ok(Self {
            config,
            registry,
            workers: HashMap::new(),
            worker_msg_tx,
            worker_msg_rx,
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

                IbcEvent::OpenInitChannel(ref _open_init) => {
                    if let Ok(object) = Object::channel_from_chan_open_events(
                        event.clone().channel_attributes().unwrap(),
                        src_chain,
                    ) {
                        collected.per_object.entry(object).or_default().push(event);
                    }
                }

                IbcEvent::OpenTryChannel(ref _open_try) => {
                    if let Ok(object) = Object::channel_from_chan_open_events(
                        event.clone().channel_attributes().unwrap(),
                        src_chain,
                    ) {
                        collected.per_object.entry(object).or_default().push(event);
                    }
                }

                IbcEvent::OpenAckChannel(ref open_ack) => {
                    // Create client worker here as channel end must be opened
                    if let Ok(object) =
                        Object::client_from_chan_open_events(open_ack.attributes(), src_chain)
                    {
                        collected
                            .per_object
                            .entry(object)
                            .or_default()
                            .push(event.clone());
                    }

                    if let Ok(channel_object) = Object::channel_from_chan_open_events(
                        event.clone().channel_attributes().unwrap(),
                        src_chain,
                    ) {
                        collected
                            .per_object
                            .entry(channel_object)
                            .or_default()
                            .push(event);
                    }
                }
                IbcEvent::OpenConfirmChannel(ref open_confirm) => {
                    // Create client worker here as channel end must be opened
                    if let Ok(object) =
                        Object::client_from_chan_open_events(open_confirm.attributes(), src_chain)
                    {
                        collected
                            .per_object
                            .entry(object)
                            .or_default()
                            .push(event.clone());
                    }
                    if let Ok(channel_object) = Object::channel_from_chan_open_events(
                        event.clone().channel_attributes().unwrap(),
                        src_chain,
                    ) {
                        collected
                            .per_object
                            .entry(channel_object)
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
            Err(Error::ConnectionNotOpen(..)) | Err(Error::ChannelUninitialized(..)) => {
                // These errors are silent.
                // Simply ignore the channel and return without spawning the workers.
                warn!(
                    " client and packet relay workers not spawned for channel/chain pair '{}'/'{}' because channel is not open",
                    channel.channel_id,
                    chain.id(),
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
            let counterparty_chain = self
                .registry
                .get_or_spawn(&client.client_state.chain_id())?;

            // create the client object and spawn worker
            let client_object = Object::Client(Client {
                dst_client_id: client.client_id.clone(),
                dst_chain_id: chain.id(),
                src_chain_id: client.client_state.chain_id(),
            });

            self.worker_for_object(client_object, chain.clone(), counterparty_chain.clone());

            // TODO: Only start the Uni worker if there are outstanding packets or ACKs.
            //  https://github.com/informalsystems/ibc-rs/issues/901
            // create the path object and spawn worker
            let path_object = Object::UnidirectionalChannelPath(UnidirectionalChannelPath {
                dst_chain_id: counterparty_chain.clone().id(),
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id.clone(),
                src_port_id: channel.port_id,
            });

            self.worker_for_object(path_object, chain.clone(), counterparty_chain.clone());
        } else {
            let counterparty_chain_id =
                get_counterparty_chain_for_channel(chain.as_ref(), channel.clone()).unwrap();

            let counterparty_chain = self.registry.get_or_spawn(&counterparty_chain_id)?;

            let channel_object = Object::Channel(Channel {
                dst_chain_id: counterparty_chain_id,
                src_chain_id: chain.id(),
                src_channel_id: channel.channel_id.clone(),
                src_port_id: channel.port_id,
                clear_pending: false,
            });

            self.worker_for_object(channel_object, chain.clone(), counterparty_chain.clone());
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
            if let Some((chain, batch)) = try_recv_multiple(&subscriptions) {
                self.handle_batch(chain.clone(), batch);
            }

            if let Ok(msg) = self.worker_msg_rx.try_recv() {
                self.handle_msg(msg);
            }

            std::thread::sleep(Duration::from_millis(50));
        }
    }

    fn handle_msg(&mut self, msg: WorkerMsg) {
        match msg {
            WorkerMsg::Stopped(object) => {
                if let Some(handle) = self.workers.remove(&object) {
                    let _ = handle.join();
                } else {
                    warn!(
                        "did not find worker handle for object '{}' after worker stopped",
                        object.short_name()
                    );
                }
            }
        }
    }

    fn handle_batch(
        &mut self,
        chain: Box<dyn ChainHandle>,
        batch: Arc<event::monitor::Result<EventBatch>>,
    ) {
        let chain_id = chain.id();

        let result = batch
            .unwrap_or_clone()
            .map_err(Into::into)
            .and_then(|batch| self.process_batch(chain, batch));

        if let Err(e) = result {
            error!("[{}] error during batch processing: {}", chain_id, e);
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
            let handles = ChainHandlePair { a: src, b: dst };
            let worker = Worker::spawn(handles, object.clone(), self.worker_msg_tx.clone());
            self.workers.entry(object).or_insert(worker)
        }
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
