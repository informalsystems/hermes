use std::{
    collections::{BTreeMap, HashMap},
    sync::{Arc, RwLock},
    time::Duration,
};

use anomaly::BoxError;
use crossbeam_channel::{Receiver, Sender};
use itertools::Itertools;
use tracing::{debug, error, info, warn};

use ibc::{events::IbcEvent, ics24_host::identifier::ChainId, Height};

use crate::{
    chain::handle::ChainHandle,
    config::{ChainConfig, Config},
    event,
    event::monitor::{EventBatch, UnwrapOrClone},
    object::Object,
    registry::Registry,
    telemetry::Telemetry,
    util::try_recv_multiple,
    worker::{WorkerMap, WorkerMsg},
};

mod error;
pub use error::Error;

pub mod dump_state;
use dump_state::SupervisorState;

pub mod spawn;
use spawn::SpawnContext;

pub mod cmd;
use cmd::{ConfigUpdate, SupervisorCmd};

type ArcBatch = Arc<event::monitor::Result<EventBatch>>;
type Subscription = Receiver<ArcBatch>;
type BoxHandle = Box<dyn ChainHandle>;

pub type RwArc<T> = Arc<RwLock<T>>;

/// The supervisor listens for events on multiple pairs of chains,
/// and dispatches the events it receives to the appropriate
/// worker, based on the [`Object`] associated with each event.
pub struct Supervisor {
    config: RwArc<Config>,
    registry: Registry,
    workers: WorkerMap,

    cmd_rx: Receiver<SupervisorCmd>,
    worker_msg_rx: Receiver<WorkerMsg>,

    #[allow(dead_code)]
    telemetry: Telemetry,
}

impl Supervisor {
    /// Create a [`Supervisor`] which will listen for events on all the chains in the [`Config`].
    pub fn new(config: RwArc<Config>, telemetry: Telemetry) -> (Self, Sender<SupervisorCmd>) {
        let registry = Registry::new(config.clone());
        let (worker_msg_tx, worker_msg_rx) = crossbeam_channel::unbounded();
        let workers = WorkerMap::new(worker_msg_tx, telemetry.clone());

        let (cmd_tx, cmd_rx) = crossbeam_channel::unbounded();

        let supervisor = Self {
            config,
            registry,
            workers,
            cmd_rx,
            worker_msg_rx,
            telemetry,
        };

        (supervisor, cmd_tx)
    }

    /// Collect the events we are interested in from an [`EventBatch`],
    /// and maps each [`IbcEvent`] to their corresponding [`Object`].
    pub fn collect_events(
        &self,
        src_chain: &dyn ChainHandle,
        batch: EventBatch,
    ) -> CollectedEvents {
        let mut collected = CollectedEvents::new(batch.height, batch.chain_id);

        let handshake_enabled = self
            .config
            .read()
            .expect("poisoned lock")
            .handshake_enabled();

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
                IbcEvent::OpenInitConnection(..)
                | IbcEvent::OpenTryConnection(..)
                | IbcEvent::OpenAckConnection(..) => {
                    if !handshake_enabled {
                        continue;
                    }

                    let object = event
                        .connection_attributes()
                        .map(|attr| Object::connection_from_conn_open_events(attr, src_chain));

                    if let Some(Ok(object)) = object {
                        collected.per_object.entry(object).or_default().push(event);
                    }
                }
                IbcEvent::OpenInitChannel(..) | IbcEvent::OpenTryChannel(..) => {
                    if !handshake_enabled {
                        continue;
                    }

                    let object = event
                        .channel_attributes()
                        .map(|attr| Object::channel_from_chan_open_events(attr, src_chain));

                    if let Some(Ok(object)) = object {
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

                    if !handshake_enabled {
                        continue;
                    }

                    let object = event
                        .channel_attributes()
                        .map(|attr| Object::channel_from_chan_open_events(attr, src_chain));

                    if let Some(Ok(object)) = object {
                        collected.per_object.entry(object).or_default().push(event);
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

    /// Create a new `SpawnContext` for spawning workers.
    fn spawn_context(&mut self) -> SpawnContext<'_> {
        SpawnContext::new(&self.config, &mut self.registry, &mut self.workers)
    }

    /// Spawn all the workers necessary for the relayer to connect
    /// and relay between all the chains in the configurations.
    fn spawn_workers(&mut self) {
        self.spawn_context().spawn_workers();
    }

    /// Run the supervisor event loop.
    pub fn run(mut self) -> Result<(), BoxError> {
        self.spawn_workers();

        let mut subscriptions = self.init_subscriptions()?;

        loop {
            if let Some((chain, batch)) = try_recv_multiple(&subscriptions) {
                self.handle_batch(chain.clone(), batch);
            }

            if let Ok(msg) = self.worker_msg_rx.try_recv() {
                self.handle_worker_msg(msg);
            }

            if let Ok(cmd) = self.cmd_rx.try_recv() {
                let after = self.handle_cmd(cmd);

                if let AfterCmd::ResetSubscriptions = after {
                    match self.init_subscriptions() {
                        Ok(subs) => {
                            subscriptions = subs;
                        }
                        Err(Error::NoChainsAvailable) => (),
                        Err(e) => return Err(e.into()),
                    }
                }
            }

            std::thread::sleep(Duration::from_millis(50));
        }
    }

    /// Subscribe to the events emitted by the chains the supervisor is connected to.
    fn init_subscriptions(&mut self) -> Result<Vec<(BoxHandle, Subscription)>, Error> {
        let chains = &self.config.read().expect("poisoned lock").chains;

        let mut subscriptions = Vec::with_capacity(chains.len());

        for chain_config in chains {
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

        // At least one chain runtime should be available, otherwise the supervisor
        // cannot do anything and will hang indefinitely.
        if self.registry.size() == 0 {
            return Err(Error::NoChainsAvailable);
        }

        Ok(subscriptions)
    }

    /// Handle the given [`SupervisorCmd`].
    ///
    /// Returns an [`AfterCmd`] which instructs the caller as to
    /// whether or not the event subscriptions needs to be reset or not.
    fn handle_cmd(&mut self, cmd: SupervisorCmd) -> AfterCmd {
        match cmd {
            SupervisorCmd::UpdateConfig(update) => self.update_config(update),
            SupervisorCmd::DumpState(reply_to) => self.dump_state(reply_to),
        }
    }

    /// Dump the state of the supervisor into a [`SupervisorState`] value,
    /// and send it back through the given channel.
    fn dump_state(&self, reply_to: Sender<SupervisorState>) -> AfterCmd {
        let mut state = SupervisorState::default();

        for chain in self.registry.chains() {
            let mut objects = self.workers.objects_for_chain(&chain.id());

            objects.sort();

            let objects_map = objects
                .into_iter()
                .into_group_map_by(|o| o.object_type())
                .into_iter()
                .collect::<BTreeMap<_, _>>();

            state.chains.insert(chain.id(), objects_map);
        }

        let _ = reply_to.try_send(state);

        AfterCmd::Nothing
    }

    /// Apply the given configuration update.
    ///
    /// Returns an [`AfterCmd`] which instructs the caller as to
    /// whether or not the event subscriptions needs to be reset or not.
    fn update_config(&mut self, update: ConfigUpdate) -> AfterCmd {
        match update {
            ConfigUpdate::Add(config) => self.add_chain(config),
            ConfigUpdate::Remove(id) => self.remove_chain(&id),
            ConfigUpdate::Update(config) => self.update_chain(config),
        }
    }

    /// Add the given chain to the configuration and spawn the associated workers.
    /// Will not have any effect if the chain is already present in the config.
    ///
    /// If the addition had any effect, returns [`AfterCmd::ResetSubscriptions`] as
    /// subscriptions need to be reset to take into account the newly added chain.
    fn add_chain(&mut self, config: ChainConfig) -> AfterCmd {
        let id = config.id.clone();

        if self.config.read().expect("poisoned lock").has_chain(&id) {
            info!(chain.id=%id, "skipping addition of already existing chain");
            return AfterCmd::Nothing;
        }

        info!(chain.id=%id, "adding new chain");

        self.config
            .write()
            .expect("poisoned lock")
            .chains
            .push(config);

        debug!(chain.id=%id, "spawning chain runtime");

        if let Err(e) = self.registry.spawn(&id) {
            error!(
                "failed to add chain {} because of failure to spawn the chain runtime: {}",
                id, e
            );

            // Remove the newly added config
            self.config
                .write()
                .expect("poisoned lock")
                .chains
                .retain(|c| c.id != id);

            return AfterCmd::Nothing;
        }

        debug!(chain.id=%id, "spawning workers");
        self.spawn_context().spawn_workers_for_chain(&id);

        AfterCmd::ResetSubscriptions
    }

    /// Remove the given chain to the configuration and spawn the associated workers.
    /// Will not have any effect if the chain was not already present in the config.
    ///
    /// If the removal had any effect, returns [`AfterCmd::ResetSubscriptions`] as
    /// subscriptions need to be reset to take into account the newly added chain.
    fn remove_chain(&mut self, id: &ChainId) -> AfterCmd {
        if !self.config.read().expect("poisoned lock").has_chain(&id) {
            info!(chain.id=%id, "skipping removal of non-existing chain");
            return AfterCmd::Nothing;
        }

        info!(chain.id=%id, "removing existing chain");

        self.config
            .write()
            .expect("poisoned lock")
            .chains
            .retain(|c| &c.id != id);

        debug!(chain.id=%id, "shutting down workers");
        self.spawn_context().shutdown_workers_for_chain(&id);

        debug!(chain.id=%id, "shutting down chain runtime");
        self.registry.shutdown(&id);

        AfterCmd::ResetSubscriptions
    }

    /// Update the given chain configuration, by removing it with
    /// [`Supervisor::remove_chain`] and adding the updated
    /// chain config with [`Supervisor::remove_chain`].
    ///
    /// If the update had any effect, returns [`AfterCmd::ResetSubscriptions`] as
    /// subscriptions need to be reset to take into account the newly added chain.
    fn update_chain(&mut self, config: ChainConfig) -> AfterCmd {
        let removed = self.remove_chain(&config.id);
        let added = self.add_chain(config);
        removed.or(added)
    }

    /// Process the given [`WorkerMsg`] sent by a worker.
    fn handle_worker_msg(&mut self, msg: WorkerMsg) {
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

    /// Process the given batch if it does not contain any errors,
    /// output the errors on the console otherwise.
    fn handle_batch(&mut self, chain: Box<dyn ChainHandle>, batch: ArcBatch) {
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum AfterCmd {
    ResetSubscriptions,
    Nothing,
}

impl AfterCmd {
    fn or(self, other: Self) -> Self {
        match (self, other) {
            (AfterCmd::ResetSubscriptions, _) => AfterCmd::ResetSubscriptions,
            (_, AfterCmd::ResetSubscriptions) => AfterCmd::ResetSubscriptions,
            _ => self,
        }
    }
}
