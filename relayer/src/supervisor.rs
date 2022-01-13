use alloc::collections::btree_map::BTreeMap as HashMap;
use alloc::sync::Arc;
use core::convert::Infallible;
use core::ops::Deref;
use core::time::Duration;
use std::sync::RwLock;

use crossbeam_channel::{unbounded, Receiver, Sender};
use itertools::Itertools;
use tracing::{debug, error, info, trace, warn};

use ibc::{
    core::ics24_host::identifier::{ChainId, ChannelId, PortId},
    events::IbcEvent,
    Height,
};

use crate::util::lock::LockExt;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::{
    chain::{handle::ChainHandle, HealthCheck},
    config::{ChainConfig, Config},
    event,
    event::monitor::{Error as EventError, ErrorDetail as EventErrorDetail, EventBatch},
    object::Object,
    registry::{Registry, SharedRegistry},
    rest,
    util::try_recv_multiple,
    worker::WorkerMap,
};

pub mod client_state_filter;
use client_state_filter::{FilterPolicy, Permission};

pub mod error;
pub use error::{Error, ErrorDetail};

pub mod dump_state;
use dump_state::SupervisorState;

pub mod spawn;
use spawn::SpawnContext;

pub mod cmd;
use cmd::{CmdEffect, ConfigUpdate, SupervisorCmd};

use self::spawn::SpawnMode;

type ArcBatch = Arc<event::monitor::Result<EventBatch>>;
type Subscription = Receiver<ArcBatch>;

/**
    A wrapper around the SupervisorCmd sender so that we can
    send stop signal to the supervisor before stopping the
    chain drivers to prevent the supervisor from raising
    errors caused by closed connections.
*/
pub struct SupervisorHandle {
    pub sender: Sender<SupervisorCmd>,
    tasks: Vec<TaskHandle>,
}

/**
   Spawn a supervisor for testing purpose using the provided
   [`SharedConfig`] and [`SharedRegistry`]. Returns a
   [`SupervisorHandle`] that stops the supervisor when the
   value is dropped.
*/
pub fn spawn_supervisor(
    config: Arc<RwLock<Config>>,
    registry: SharedRegistry<impl ChainHandle>,
    rest_rx: Option<rest::Receiver>,
    do_health_check: bool,
) -> Result<SupervisorHandle, Error> {
    let (sender, receiver) = unbounded();

    let tasks = spawn_supervisor_tasks(config, registry, rest_rx, receiver, do_health_check)?;

    Ok(SupervisorHandle { sender, tasks })
}

impl SupervisorHandle {
    /**
       Explicitly stop the running supervisor. This is useful in tests where
       the supervisor has to be stopped and restarted explicitly.

       Note that after stopping the supervisor, the only way to restart it
       is by respawning a new supervisor using [`spawn_supervisor`].
    */
    pub fn shutdown(self) {
        for task in self.tasks {
            // Send the shutdown signals in parallel
            task.shutdown();
        }
        // Dropping the tasks will cause this to block until all tasks
        // are terminated.
    }

    pub fn wait(self) {
        for task in self.tasks {
            task.join();
        }
    }
}

pub fn spawn_supervisor_tasks<Chain: ChainHandle>(
    config: Arc<RwLock<Config>>,
    registry: SharedRegistry<Chain>,
    rest_rx: Option<rest::Receiver>,
    cmd_rx: Receiver<SupervisorCmd>,
    do_health_check: bool,
) -> Result<Vec<TaskHandle>, Error> {
    if do_health_check {
        health_check(&config.acquire_read(), &mut registry.write());
    }

    let workers = Arc::new(RwLock::new(WorkerMap::new()));
    let client_state_filter = Arc::new(RwLock::new(FilterPolicy::default()));

    spawn_context(
        &config.acquire_read(),
        &mut registry.write(),
        &mut client_state_filter.acquire_write(),
        &mut workers.acquire_write(),
        SpawnMode::Startup,
    )
    .spawn_workers();

    let subscriptions = Arc::new(RwLock::new(init_subscriptions(
        &config.acquire_read(),
        &mut registry.write(),
    )?));

    let batch_task = spawn_batch_worker(
        config.clone(),
        registry.clone(),
        client_state_filter.clone(),
        workers.clone(),
        subscriptions.clone(),
    );

    let cmd_task = spawn_cmd_worker(
        config.clone(),
        registry.clone(),
        client_state_filter,
        workers.clone(),
        subscriptions,
        cmd_rx,
    );

    let mut tasks = vec![batch_task, cmd_task];

    if let Some(rest_rx) = rest_rx {
        let rest_task = spawn_rest_worker(config, registry, workers, rest_rx);
        tasks.push(rest_task);
    }

    Ok(tasks)
}

fn spawn_batch_worker<Chain: ChainHandle>(
    config: Arc<RwLock<Config>>,
    registry: SharedRegistry<Chain>,
    client_state_filter: Arc<RwLock<FilterPolicy>>,
    workers: Arc<RwLock<WorkerMap>>,
    subscriptions: Arc<RwLock<Vec<(Chain, Subscription)>>>,
) -> TaskHandle {
    spawn_background_task(
        "supervisor_batch".to_string(),
        Some(Duration::from_millis(500)),
        move || -> Result<Next, TaskError<Infallible>> {
            if let Some((chain, batch)) = try_recv_multiple(&subscriptions.acquire_read()) {
                handle_batch(
                    &config.acquire_read(),
                    &mut registry.write(),
                    &mut client_state_filter.acquire_write(),
                    &mut workers.acquire_write(),
                    chain.clone(),
                    batch,
                );
            }

            Ok(Next::Continue)
        },
    )
}

pub fn spawn_cmd_worker<Chain: ChainHandle>(
    config: Arc<RwLock<Config>>,
    registry: SharedRegistry<Chain>,
    client_state_filter: Arc<RwLock<FilterPolicy>>,
    workers: Arc<RwLock<WorkerMap>>,
    subscriptions: Arc<RwLock<Vec<(Chain, Subscription)>>>,
    cmd_rx: Receiver<SupervisorCmd>,
) -> TaskHandle {
    spawn_background_task(
        "supervisor_cmd".to_string(),
        Some(Duration::from_millis(500)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                match cmd {
                    SupervisorCmd::UpdateConfig(update) => {
                        let effect = update_config(
                            &mut config.acquire_write(),
                            &mut registry.write(),
                            &mut workers.acquire_write(),
                            &mut client_state_filter.acquire_write(),
                            *update,
                        );

                        if let CmdEffect::ConfigChanged = effect {
                            let new_subscriptions =
                                init_subscriptions(&config.acquire_read(), &mut registry.write());
                            match new_subscriptions {
                                Ok(subs) => {
                                    *subscriptions.acquire_write() = subs;
                                }
                                Err(Error(ErrorDetail::NoChainsAvailable(_), _)) => (),
                                Err(e) => return Err(TaskError::Fatal(e)),
                            }
                        }
                    }
                    SupervisorCmd::DumpState(reply_to) => {
                        dump_state(&registry.read(), &workers.acquire_read(), reply_to);
                    }
                }
            }
            Ok(Next::Continue)
        },
    )
}

pub fn spawn_rest_worker<Chain: ChainHandle>(
    config: Arc<RwLock<Config>>,
    registry: SharedRegistry<Chain>,
    workers: Arc<RwLock<WorkerMap>>,
    rest_rx: rest::Receiver,
) -> TaskHandle {
    spawn_background_task(
        "supervisor_rest".to_string(),
        Some(Duration::from_millis(500)),
        move || -> Result<Next, TaskError<Infallible>> {
            handle_rest_requests(
                &config.acquire_read(),
                &registry.read(),
                &workers.acquire_read(),
                &rest_rx,
            );

            Ok(Next::Continue)
        },
    )
}

/// Returns `true` if the relayer should filter based on
/// client state attributes, e.g., trust threshold.
/// Returns `false` otherwise.
fn client_filter_enabled(config: &Config) -> bool {
    // Currently just a wrapper over the global filter.
    config.mode.packets.filter
}

/// Returns `true` if the relayer should filter based on
/// channel identifiers.
/// Returns `false` otherwise.
fn channel_filter_enabled(config: &Config) -> bool {
    config.mode.packets.filter
}

fn relay_packets_on_channel(
    config: &Config,
    chain_id: &ChainId,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> bool {
    // If filtering is disabled, then relay all channels
    if !channel_filter_enabled(config) {
        return true;
    }

    config.packets_on_channel_allowed(chain_id, port_id, channel_id)
}

fn relay_on_object<Chain: ChainHandle>(
    config: &Config,
    registry: &mut Registry<Chain>,
    client_state_filter: &mut FilterPolicy,
    chain_id: &ChainId,
    object: &Object,
) -> bool {
    // No filter is enabled, bail fast.
    if !channel_filter_enabled(config) && !client_filter_enabled(config) {
        return true;
    }

    // First, apply the channel filter
    if let Object::Packet(u) = object {
        if !relay_packets_on_channel(config, chain_id, u.src_port_id(), u.src_channel_id()) {
            return false;
        }
    }

    // Second, apply the client filter
    let client_filter_outcome = match object {
        Object::Client(client) => client_state_filter.control_client_object(registry, client),
        Object::Connection(conn) => client_state_filter.control_conn_object(registry, conn),
        Object::Channel(chan) => client_state_filter.control_chan_object(registry, chan),
        Object::Packet(u) => client_state_filter.control_packet_object(registry, u),
    };

    match client_filter_outcome {
        Ok(Permission::Allow) => true,
        Ok(Permission::Deny) => {
            warn!(
                "client filter denies relaying on object {}",
                object.short_name()
            );

            false
        }
        Err(e) => {
            warn!(
                "denying relaying on object {}, caused by: {}",
                object.short_name(),
                e
            );

            false
        }
    }
}

/// If `enabled`, build an `Object` using the provided `object_ctor`
/// and add the given `event` to the `collected` events for this `object`.
fn collect_event<F>(
    collected: &mut CollectedEvents,
    event: &IbcEvent,
    enabled: bool,
    object_ctor: F,
) where
    F: FnOnce() -> Option<Object>,
{
    if enabled {
        if let Some(object) = object_ctor() {
            collected
                .per_object
                .entry(object)
                .or_default()
                .push(event.clone());
        }
    }
}

fn collect_events(
    config: &Config,
    workers: &WorkerMap,
    src_chain: &impl ChainHandle,
    batch: &EventBatch,
) -> CollectedEvents {
    let mut collected = CollectedEvents::new(batch.height, batch.chain_id.clone());

    let mode = config.mode;

    for event in &batch.events {
        match event {
            IbcEvent::NewBlock(_) => {
                collected.new_block = Some(event.clone());
            }
            IbcEvent::UpdateClient(ref update) => {
                collect_event(&mut collected, event, mode.clients.enabled, || {
                    // Collect update client events only if the worker exists
                    if let Ok(object) = Object::for_update_client(update, src_chain) {
                        workers.contains(&object).then(|| object)
                    } else {
                        None
                    }
                });
            }
            IbcEvent::OpenInitConnection(..)
            | IbcEvent::OpenTryConnection(..)
            | IbcEvent::OpenAckConnection(..) => {
                collect_event(&mut collected, event, mode.connections.enabled, || {
                    event
                        .connection_attributes()
                        .map(|attr| Object::connection_from_conn_open_events(attr, src_chain).ok())
                        .flatten()
                });
            }
            IbcEvent::OpenInitChannel(..) | IbcEvent::OpenTryChannel(..) => {
                collect_event(&mut collected, event, mode.channels.enabled, || {
                    event
                        .channel_attributes()
                        .map(|attr| Object::channel_from_chan_open_events(attr, src_chain).ok())
                        .flatten()
                });
            }
            IbcEvent::OpenAckChannel(ref open_ack) => {
                // Create client and packet workers here as channel end must be opened
                collect_event(&mut collected, event, mode.clients.enabled, || {
                    Object::client_from_chan_open_events(open_ack.attributes(), src_chain).ok()
                });

                collect_event(&mut collected, event, mode.packets.enabled, || {
                    Object::packet_from_chan_open_events(open_ack.attributes(), src_chain).ok()
                });

                // If handshake message relaying is enabled create worker to send the MsgChannelOpenConfirm message
                collect_event(&mut collected, event, mode.channels.enabled, || {
                    Object::channel_from_chan_open_events(open_ack.attributes(), src_chain).ok()
                });
            }
            IbcEvent::OpenConfirmChannel(ref open_confirm) => {
                // Create client worker here as channel end must be opened
                collect_event(&mut collected, event, mode.clients.enabled, || {
                    Object::client_from_chan_open_events(open_confirm.attributes(), src_chain).ok()
                });

                collect_event(&mut collected, event, mode.packets.enabled, || {
                    Object::packet_from_chan_open_events(open_confirm.attributes(), src_chain).ok()
                });
            }
            IbcEvent::SendPacket(ref packet) => {
                collect_event(&mut collected, event, mode.packets.enabled, || {
                    Object::for_send_packet(packet, src_chain).ok()
                });
            }
            IbcEvent::TimeoutPacket(ref packet) => {
                collect_event(&mut collected, event, mode.packets.enabled, || {
                    Object::for_timeout_packet(packet, src_chain).ok()
                });
            }
            IbcEvent::WriteAcknowledgement(ref packet) => {
                collect_event(&mut collected, event, mode.packets.enabled, || {
                    Object::for_write_ack(packet, src_chain).ok()
                });
            }
            IbcEvent::CloseInitChannel(ref packet) => {
                collect_event(&mut collected, event, mode.packets.enabled, || {
                    Object::for_close_init_channel(packet, src_chain).ok()
                });
            }
            _ => (),
        }
    }

    collected
}

/// Create a new `SpawnContext` for spawning workers.
fn spawn_context<'a, Chain: ChainHandle>(
    config: &'a Config,
    registry: &'a mut Registry<Chain>,
    client_state_filter: &'a mut FilterPolicy,
    workers: &'a mut WorkerMap,
    mode: SpawnMode,
) -> SpawnContext<'a, Chain> {
    SpawnContext::new(config, registry, client_state_filter, workers, mode)
}

/// Perform a health check on all connected chains
fn health_check<Chain: ChainHandle>(config: &Config, registry: &mut Registry<Chain>) {
    use HealthCheck::*;

    let chains = &config.chains;

    for config in chains {
        let id = &config.id;
        let chain = registry.get_or_spawn(id);

        match chain {
            Ok(chain) => match chain.health_check() {
                Ok(Healthy) => info!("[{}] chain is healthy", id),
                Ok(Unhealthy(e)) => warn!("[{}] chain is unhealthy: {}", id, e),
                Err(e) => error!("[{}] failed to perform health check: {}", id, e),
            },
            Err(e) => {
                error!(
                    "skipping health check for chain {}, reason: failed to spawn chain runtime with error: {}",
                    config.id, e
                );
            }
        }
    }
}

/// Subscribe to the events emitted by the chains the supervisor is connected to.
fn init_subscriptions<Chain: ChainHandle>(
    config: &Config,
    registry: &mut Registry<Chain>,
) -> Result<Vec<(Chain, Subscription)>, Error> {
    let chains = &config.chains;

    let mut subscriptions = Vec::with_capacity(chains.len());

    for chain_config in chains {
        let chain = match registry.get_or_spawn(&chain_config.id) {
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
    if registry.size() == 0 {
        return Err(Error::no_chains_available());
    }

    Ok(subscriptions)
}

/// Dump the state of the supervisor into a [`SupervisorState`] value,
/// and send it back through the given channel.
fn dump_state<Chain: ChainHandle>(
    registry: &Registry<Chain>,
    workers: &WorkerMap,
    reply_to: Sender<SupervisorState>,
) {
    let state = state(registry, workers);
    let _ = reply_to.try_send(state);
}

/// Returns a representation of the supervisor's internal state
/// as a [`SupervisorState`].
fn state<Chain: ChainHandle>(registry: &Registry<Chain>, workers: &WorkerMap) -> SupervisorState {
    let chains = registry.chains().map(|c| c.id()).collect_vec();
    SupervisorState::new(chains, workers.objects())
}

fn handle_rest_requests<Chain: ChainHandle>(
    config: &Config,
    registry: &Registry<Chain>,
    workers: &WorkerMap,
    rest_rx: &rest::Receiver,
) {
    if let Some(cmd) = rest::process_incoming_requests(config, rest_rx) {
        handle_rest_cmd(registry, workers, cmd);
    }
}

fn handle_rest_cmd<Chain: ChainHandle>(
    registry: &Registry<Chain>,
    workers: &WorkerMap,
    m: rest::Command,
) {
    match m {
        rest::Command::DumpState(reply) => {
            let state = state(registry, workers);
            reply.send(Ok(state)).unwrap_or_else(|e| {
                error!("[rest/supervisor] error replying to a REST request {}", e)
            });
        }
    }
}

fn clear_pending_packets(workers: &mut WorkerMap, chain_id: &ChainId) -> Result<(), Error> {
    for worker in workers.workers_for_chain(chain_id) {
        worker.clear_pending_packets();
    }

    Ok(())
}

/// Process a batch of events received from a chain.
fn process_batch<Chain: ChainHandle>(
    config: &Config,
    registry: &mut Registry<Chain>,
    client_state_filter: &mut FilterPolicy,
    workers: &mut WorkerMap,
    src_chain: Chain,
    batch: &EventBatch,
) -> Result<(), Error> {
    assert_eq!(src_chain.id(), batch.chain_id);

    let height = batch.height;
    let chain_id = batch.chain_id.clone();

    let collected = collect_events(config, workers, &src_chain, batch);

    // If there is a NewBlock event, forward this event first to any workers affected by it.
    if let Some(IbcEvent::NewBlock(new_block)) = collected.new_block {
        workers.notify_new_block(&src_chain.id(), height, new_block);
    }

    // Forward the IBC events.
    for (object, events) in collected.per_object.into_iter() {
        if !relay_on_object(
            config,
            registry,
            client_state_filter,
            &src_chain.id(),
            &object,
        ) {
            trace!(
                "skipping events for '{}'. \
                reason: filtering is enabled and channel does not match any allowed channels",
                object.short_name()
            );

            continue;
        }

        if events.is_empty() {
            continue;
        }

        let src = registry
            .get_or_spawn(object.src_chain_id())
            .map_err(Error::spawn)?;

        let dst = registry
            .get_or_spawn(object.dst_chain_id())
            .map_err(Error::spawn)?;

        let worker = workers.get_or_spawn(object, src, dst, config);

        worker.send_events(height, events, chain_id.clone());
    }

    Ok(())
}

/// Process the given batch if it does not contain any errors,
/// output the errors on the console otherwise.
fn handle_batch<Chain: ChainHandle>(
    config: &Config,
    registry: &mut Registry<Chain>,
    client_state_filter: &mut FilterPolicy,
    workers: &mut WorkerMap,
    chain: Chain,
    batch: ArcBatch,
) {
    let chain_id = chain.id();

    match batch.deref() {
        Ok(batch) => {
            let _ = process_batch(config, registry, client_state_filter, workers, chain, batch)
                .map_err(|e| error!("[{}] error during batch processing: {}", chain_id, e));
        }
        Err(EventError(EventErrorDetail::SubscriptionCancelled(_), _)) => {
            warn!(chain.id = %chain_id, "event subscription was cancelled, clearing pending packets");

            let _ = clear_pending_packets(workers, &chain_id).map_err(|e| {
                error!(
                    "[{}] error during clearing pending packets: {}",
                    chain_id, e
                )
            });
        }
        Err(e) => {
            error!("[{}] error in receiving event batch: {}", chain_id, e)
        }
    }
}

/// Remove the given chain to the configuration and spawn the associated workers.
/// Will not have any effect if the chain was not already present in the config.
///
/// If the removal had any effect, returns [`CmdEffect::ConfigChanged`] as
/// subscriptions need to be reset to take into account the newly added chain.
fn remove_chain<Chain: ChainHandle>(
    config: &mut Config,
    registry: &mut Registry<Chain>,
    workers: &mut WorkerMap,
    client_state_filter: &mut FilterPolicy,
    id: &ChainId,
) -> CmdEffect {
    if !config.has_chain(id) {
        info!(chain.id=%id, "skipping removal of non-existing chain");
        return CmdEffect::Nothing;
    }

    info!(chain.id=%id, "removing existing chain");

    config.chains.retain(|c| &c.id != id);

    debug!(chain.id=%id, "shutting down workers");

    let mut ctx = spawn_context(
        config,
        registry,
        client_state_filter,
        workers,
        SpawnMode::Reload,
    );

    ctx.shutdown_workers_for_chain(id);

    debug!(chain.id=%id, "shutting down chain runtime");
    registry.shutdown(id);

    CmdEffect::ConfigChanged
}

/// Add the given chain to the configuration and spawn the associated workers.
/// Will not have any effect if the chain is already present in the config.
///
/// If the addition had any effect, returns [`CmdEffect::ConfigChanged`] as
/// subscriptions need to be reset to take into account the newly added chain.
fn add_chain<Chain: ChainHandle>(
    config: &mut Config,
    registry: &mut Registry<Chain>,
    workers: &mut WorkerMap,
    client_state_filter: &mut FilterPolicy,
    chain_config: ChainConfig,
) -> CmdEffect {
    let id = chain_config.id.clone();

    if config.has_chain(&id) {
        info!(chain.id=%id, "skipping addition of already existing chain");
        return CmdEffect::Nothing;
    }

    info!(chain.id=%id, "adding new chain");

    config.chains.push(chain_config);

    debug!(chain.id=%id, "spawning chain runtime");

    if let Err(e) = registry.spawn(&id) {
        error!(
            "failed to add chain {} because of failure to spawn the chain runtime: {}",
            id, e
        );

        // Remove the newly added config
        config.chains.retain(|c| c.id != id);

        return CmdEffect::Nothing;
    }

    debug!(chain.id=%id, "spawning workers");

    let mut ctx = spawn_context(
        config,
        registry,
        client_state_filter,
        workers,
        SpawnMode::Reload,
    );

    ctx.spawn_workers_for_chain(&id);

    CmdEffect::ConfigChanged
}

/// Update the given chain configuration, by removing it with
/// [`Supervisor::remove_chain`] and adding the updated
/// chain config with [`Supervisor::remove_chain`].
///
/// If the update had any effect, returns [`CmdEffect::ConfigChanged`] as
/// subscriptions need to be reset to take into account the newly added chain.
fn update_chain<Chain: ChainHandle>(
    config: &mut Config,
    registry: &mut Registry<Chain>,
    workers: &mut WorkerMap,
    client_state_filter: &mut FilterPolicy,
    chain_config: ChainConfig,
) -> CmdEffect {
    info!(chain.id=%chain_config.id, "updating existing chain");

    let removed = remove_chain(
        config,
        registry,
        workers,
        client_state_filter,
        &chain_config.id,
    );

    let added = add_chain(config, registry, workers, client_state_filter, chain_config);

    removed.or(added)
}

/// Apply the given configuration update.
///
/// Returns an [`CmdEffect`] which instructs the caller as to
/// whether or not the event subscriptions needs to be reset or not.
fn update_config<Chain: ChainHandle>(
    config: &mut Config,
    registry: &mut Registry<Chain>,
    workers: &mut WorkerMap,
    client_state_filter: &mut FilterPolicy,
    update: ConfigUpdate,
) -> CmdEffect {
    match update {
        ConfigUpdate::Add(chain_config) => {
            add_chain(config, registry, workers, client_state_filter, chain_config)
        }
        ConfigUpdate::Remove(id) => {
            remove_chain(config, registry, workers, client_state_filter, &id)
        }
        ConfigUpdate::Update(chain_config) => {
            update_chain(config, registry, workers, client_state_filter, chain_config)
        }
    }
}

/// Describes the result of [`collect_events`](Supervisor::collect_events).
#[derive(Clone, Debug)]
pub struct CollectedEvents {
    /// The height at which these events were emitted from the chain.
    pub height: Height,
    /// The chain from which the events were emitted.
    pub chain_id: ChainId,
    /// [`NewBlock`](ibc::events::IbcEventType::NewBlock) event
    /// collected from the [`EventBatch`].
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

    /// Whether the collected events include a
    /// [`NewBlock`](ibc::events::IbcEventType::NewBlock) event.
    pub fn has_new_block(&self) -> bool {
        self.new_block.is_some()
    }
}
