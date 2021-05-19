use std::{collections::HashMap, sync::Arc, time::Duration};

use anomaly::BoxError;

use crossbeam_channel::Receiver;
use itertools::Itertools;
use tracing::{debug, error, trace, warn};

use ibc::{
    events::{IbcEvent, VecIbcEvents},
    ics02_client::client_state::ClientState,
    ics04_channel::channel::IdentifiedChannelEnd,
    ics24_host::identifier::ChainId,
    Height,
};

use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;

use crate::{
    chain::{counterparty::channel_connection_client, handle::ChainHandle},
    config::Config,
    event::{
        self,
        monitor::{EventBatch, UnwrapOrClone},
    },
    object::{Client, Object, UnidirectionalChannelPath},
    registry::Registry,
    rest,
    util::try_recv_multiple,
    worker::{WorkerMap, WorkerMsg},
};

mod error;
pub use error::Error;

/// The supervisor listens for events on multiple pairs of chains,
/// and dispatches the events it receives to the appropriate
/// worker, based on the [`Object`] associated with each event.
pub struct Supervisor {
    config: Config,
    registry: Registry,
    workers: WorkerMap,
    worker_msg_rx: Receiver<WorkerMsg>,
    rest_receiver: Receiver<rest::Request>,
}

impl Supervisor {
    /// Spawns a [`Supervisor`] which will listen for events on all the chains in the [`Config`].
    pub fn spawn(config: Config, rest_receiver: Receiver<rest::Request>) -> Result<Self, BoxError> {
        let registry = Registry::new(config.clone());
        let (worker_msg_tx, worker_msg_rx) = crossbeam_channel::unbounded();

        Ok(Self {
            config,
            registry,
            workers: WorkerMap::new(worker_msg_tx),
            worker_msg_rx,
            rest_receiver,
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
                        if self.workers.contains(&object) {
                            collected.per_object.entry(object).or_default().push(event);
                        }
                    }
                }
                IbcEvent::OpenAckChannel(ref open_ack) => {
                    // Create client worker here as channel end must be opened
                    if let Ok(object) =
                        Object::for_chan_open_events(open_ack.attributes(), src_chain)
                    {
                        collected.per_object.entry(object).or_default().push(event);
                    }
                }
                IbcEvent::OpenConfirmChannel(ref open_confirm) => {
                    // Create client worker here as channel end must be opened
                    if let Ok(object) =
                        Object::for_chan_open_events(open_confirm.attributes(), src_chain)
                    {
                        collected.per_object.entry(object).or_default().push(event);
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

        let client = match client_res {
            Ok(conn_client) => conn_client.client,
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

        let counterparty_chain = self
            .registry
            .get_or_spawn(&client.client_state.chain_id())?;

        // create the client object and spawn worker
        let client_object = Object::Client(Client {
            dst_client_id: client.client_id.clone(),
            dst_chain_id: chain.id(),
            src_chain_id: client.client_state.chain_id(),
        });

        self.workers
            .get_or_spawn(client_object, chain.clone(), counterparty_chain.clone());

        // TODO: Only start the Uni worker if there are outstanding packets or ACKs.
        //  https://github.com/informalsystems/ibc-rs/issues/901
        // create the path object and spawn worker
        let path_object = Object::UnidirectionalChannelPath(UnidirectionalChannelPath {
            dst_chain_id: counterparty_chain.id(),
            src_chain_id: chain.id(),
            src_channel_id: channel.channel_id.clone(),
            src_port_id: channel.port_id,
        });

        self.workers
            .get_or_spawn(path_object, chain.clone(), counterparty_chain.clone());

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

            if let Some(msg) = rest::process(&self.config, &self.rest_receiver) {
                self.handle_rest_request(msg);
            }

            std::thread::sleep(Duration::from_millis(50));
        }
    }

    fn handle_msg(&mut self, msg: WorkerMsg) {
        match msg {
            WorkerMsg::Stopped(object) => {
                if !self.workers.remove_stopped(&object) {
                    warn!(
                        "did not find worker handle for object '{}' after worker stopped",
                        object.short_name()
                    );
                }
            }
        }
    }

    fn handle_rest_request(&mut self, _m: rest::Msg) {
        todo!()
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

            debug!(
                "chain {} sent {} for object {:?}",
                chain_id,
                VecIbcEvents(events.clone()),
                object,
            );

            let src = self.registry.get_or_spawn(object.src_chain_id())?;
            let dst = self.registry.get_or_spawn(object.dst_chain_id())?;

            let worker = self.workers.get_or_spawn(object, src, dst);
            worker.send_events(height, events, chain_id.clone())?
        }

        // If there is a NewBlock event, forward the event to any workers affected by it.
        if let Some(IbcEvent::NewBlock(new_block)) = collected.new_block {
            for worker in self.workers.to_notify(&src_chain.id()) {
                worker.send_new_block(height, new_block)?;
            }
        }

        Ok(())
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
