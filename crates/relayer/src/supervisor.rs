use alloc::collections::btree_map::BTreeMap as HashMap;
use alloc::sync::Arc;
use core::convert::Infallible;
use core::ops::Deref;
use core::time::Duration;
use std::sync::RwLock;

use crossbeam_channel::{unbounded, Receiver, Sender};
use itertools::Itertools;
use tracing::{debug, error, error_span, info, instrument, trace, warn};

use ibc_relayer_types::{
    core::ics24_host::identifier::{ChainId, ChannelId, PortId},
    events::IbcEvent,
    Height,
};

use crate::{
    chain::{endpoint::HealthCheck, handle::ChainHandle, tracking::TrackingId},
    config::Config,
    event::{
        monitor::{self, Error as EventError, ErrorDetail as EventErrorDetail, EventBatch},
        IbcEventWithHeight,
    },
    object::Object,
    registry::{Registry, SharedRegistry},
    rest,
    supervisor::scan::ScanMode,
    telemetry,
    util::{
        lock::LockExt,
        task::{spawn_background_task, Next, TaskError, TaskHandle},
    },
    worker::WorkerMap,
};

pub mod client_state_filter;
use client_state_filter::{FilterPolicy, Permission};

pub mod error;
pub use error::{Error, ErrorDetail};

pub mod dump_state;
use dump_state::SupervisorState;

pub mod scan;
pub mod spawn;

pub mod cmd;
use cmd::SupervisorCmd;

use self::{scan::ChainScanner, spawn::SpawnContext};

type ArcBatch = Arc<monitor::Result<EventBatch>>;
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

/// Options for the supervisor
#[derive(Debug)]
pub struct SupervisorOptions {
    /// Perform a health check of all chains we connect to
    pub health_check: bool,

    /// Force a full scan of the chains for clients, connections, and channels,
    /// even when an allow list is configured for a chain and the full scan could
    /// be omitted.
    pub force_full_scan: bool,
}

/**
   Spawn a supervisor for testing purpose using the provided
   [`Config`] and [`SharedRegistry`]. Returns a
   [`SupervisorHandle`] that stops the supervisor when the
   value is dropped.
*/
pub fn spawn_supervisor(
    config: Config,
    registry: SharedRegistry<impl ChainHandle>,
    rest_rx: Option<rest::Receiver>,
    options: SupervisorOptions,
) -> Result<SupervisorHandle, Error> {
    let (sender, receiver) = unbounded();

    let tasks = spawn_supervisor_tasks(config, registry, rest_rx, receiver, options)?;

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

    /// Ask the supervisor to dump its internal state
    pub fn dump_state(&self) -> Result<SupervisorState, Error> {
        let (tx, rx) = crossbeam_channel::bounded(1);

        self.sender
            .send(SupervisorCmd::DumpState(tx))
            .map_err(|_| Error::handle_send())?;

        let state = rx.recv().map_err(|_| Error::handle_recv())?;

        Ok(state)
    }
}

pub fn spawn_supervisor_tasks<Chain: ChainHandle>(
    config: Config,
    registry: SharedRegistry<Chain>,
    rest_rx: Option<rest::Receiver>,
    cmd_rx: Receiver<SupervisorCmd>,
    options: SupervisorOptions,
) -> Result<Vec<TaskHandle>, Error> {
    if options.health_check {
        health_check(&config, &mut registry.write());
    }

    let workers = Arc::new(RwLock::new(WorkerMap::new()));
    let client_state_filter = Arc::new(RwLock::new(FilterPolicy::default()));

    let scan = chain_scanner(
        &config,
        &mut registry.write(),
        &mut client_state_filter.acquire_write(),
        if options.force_full_scan {
            ScanMode::Full
        } else {
            ScanMode::Auto
        },
    )
    .scan_chains();

    info!("scanned chains:");
    info!("{}", scan);

    spawn_context(&config, &mut registry.write(), &mut workers.acquire_write()).spawn_workers(scan);

    let subscriptions = init_subscriptions(&config, &mut registry.write())?;

    let batch_tasks = spawn_batch_workers(
        &config,
        registry.clone(),
        client_state_filter,
        workers.clone(),
        subscriptions,
    );

    let cmd_task = spawn_cmd_worker(registry.clone(), workers.clone(), cmd_rx);

    let mut tasks = vec![cmd_task];
    tasks.extend(batch_tasks);

    if let Some(rest_rx) = rest_rx {
        let rest_task = spawn_rest_worker(config, registry, workers, rest_rx);
        tasks.push(rest_task);
    }

    Ok(tasks)
}

fn spawn_batch_workers<Chain: ChainHandle>(
    config: &Config,
    registry: SharedRegistry<Chain>,
    client_state_filter: Arc<RwLock<FilterPolicy>>,
    workers: Arc<RwLock<WorkerMap>>,
    subscriptions: Vec<(Chain, Subscription)>,
) -> Vec<TaskHandle> {
    let mut handles = Vec::with_capacity(subscriptions.len());

    for (chain, subscription) in subscriptions {
        let config = config.clone();
        let registry = registry.clone();
        let client_state_filter = client_state_filter.clone();
        let workers = workers.clone();

        let handle = spawn_background_task(
            error_span!("worker.batch", chain = %chain.id()),
            Some(Duration::from_millis(5)),
            move || -> Result<Next, TaskError<Infallible>> {
                if let Ok(batch) = subscription.try_recv() {
                    handle_batch(
                        &config,
                        &mut registry.write(),
                        &mut client_state_filter.acquire_write(),
                        &mut workers.acquire_write(),
                        chain.clone(),
                        batch,
                    );
                }

                Ok(Next::Continue)
            },
        );

        handles.push(handle);
    }

    handles
}

pub fn spawn_cmd_worker<Chain: ChainHandle>(
    registry: SharedRegistry<Chain>,
    workers: Arc<RwLock<WorkerMap>>,
    cmd_rx: Receiver<SupervisorCmd>,
) -> TaskHandle {
    spawn_background_task(
        error_span!("worker.cmd"),
        Some(Duration::from_millis(500)),
        move || -> Result<Next, TaskError<Infallible>> {
            if let Ok(cmd) = cmd_rx.try_recv() {
                match cmd {
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
    config: Config,
    registry: SharedRegistry<Chain>,
    workers: Arc<RwLock<WorkerMap>>,
    rest_rx: rest::Receiver,
) -> TaskHandle {
    spawn_background_task(
        error_span!("rest"),
        Some(Duration::from_millis(500)),
        move || -> Result<Next, TaskError<Infallible>> {
            handle_rest_requests(&config, &registry.read(), &workers.acquire_read(), &rest_rx);

            Ok(Next::Continue)
        },
    )
}

/// Returns `true` if the relayer should filter based on
/// client state attributes, e.g., trust threshold.
/// Returns `false` otherwise.
fn client_filter_enabled(_config: &Config) -> bool {
    // we currently always enable the client filter
    true
}

/// Returns `true` if the relayer should filter based on
/// channel identifiers.
/// Returns `false` otherwise.
fn channel_filter_enabled(_config: &Config) -> bool {
    // we currently always enable the channel filter
    true
}

/// Whether or not the given channel is allowed by the filter policy, if any.
fn is_channel_allowed(
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

/// Whether or not the relayer should relay packets
/// or complete handshakes for the given [`Object`].
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

    // First, apply the channel filter on packets and channel workers
    match object {
        Object::Packet(p) => {
            if !is_channel_allowed(config, chain_id, &p.src_port_id, &p.src_channel_id) {
                // Forbid relaying packets on that channel
                return false;
            }
        }
        Object::Channel(c) => {
            if !is_channel_allowed(config, chain_id, &c.src_port_id, &c.src_channel_id) {
                // Forbid completing handshake for that channel
                return false;
            }
        }
        _ => (),
    };

    // Then, apply the client filter
    let client_filter_outcome = match object {
        Object::Client(client) => client_state_filter.control_client_object(registry, client),
        Object::Connection(conn) => client_state_filter.control_conn_object(registry, conn),
        Object::Channel(chan) => client_state_filter.control_chan_object(registry, chan),
        Object::Packet(packet) => client_state_filter.control_packet_object(registry, packet),
        Object::Wallet(_wallet) => Ok(Permission::Allow),
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
        Err(e) if e.log_as_debug() => {
            debug!(
                "denying relaying on object {}, caused by: {}",
                object.short_name(),
                e
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
    event_with_height: IbcEventWithHeight,
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
                .push(event_with_height);
        }
    }
}

pub fn collect_events(
    config: &Config,
    workers: &WorkerMap,
    src_chain: &impl ChainHandle,
    batch: &EventBatch,
) -> CollectedEvents {
    let mut collected =
        CollectedEvents::new(batch.height, batch.chain_id.clone(), batch.tracking_id);

    let mode = config.mode;

    for event_with_height in &batch.events {
        match &event_with_height.event {
            IbcEvent::NewBlock(_) => {
                collected.new_block = Some(event_with_height.event.clone());
            }
            IbcEvent::UpdateClient(update) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.clients.enabled,
                    || {
                        // Collect update client events only if the worker exists
                        if let Ok(object) = Object::for_update_client(update, src_chain) {
                            workers.contains(&object).then_some(object)
                        } else {
                            None
                        }
                    },
                );
            }
            IbcEvent::OpenInitConnection(..)
            | IbcEvent::OpenTryConnection(..)
            | IbcEvent::OpenAckConnection(..) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.connections.enabled,
                    || {
                        event_with_height
                            .event
                            .connection_attributes()
                            .and_then(|attr| {
                                Object::connection_from_conn_open_events(attr, src_chain).ok()
                            })
                    },
                );
            }
            IbcEvent::OpenInitChannel(..) | IbcEvent::OpenTryChannel(..) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.channels.enabled,
                    || {
                        event_with_height
                            .event
                            .clone()
                            .channel_attributes()
                            .and_then(|attr| {
                                Object::channel_from_chan_open_events(&attr, src_chain).ok()
                            })
                    },
                );
            }
            IbcEvent::OpenAckChannel(open_ack) => {
                // Create client and packet workers here as channel end must be opened
                let attributes = open_ack.clone().into();
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.clients.enabled,
                    || Object::client_from_chan_open_events(&attributes, src_chain).ok(),
                );

                // If handshake message relaying is enabled create worker to send the MsgChannelOpenConfirm message
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.channels.enabled,
                    || Object::channel_from_chan_open_events(&attributes, src_chain).ok(),
                );
            }
            IbcEvent::OpenConfirmChannel(open_confirm) => {
                let attributes = open_confirm.clone().into();
                // Create client worker here as channel end must be opened
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.clients.enabled,
                    || Object::client_from_chan_open_events(&attributes, src_chain).ok(),
                );
            }
            IbcEvent::SendPacket(ref packet) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.packets.enabled,
                    || Object::for_send_packet(packet, src_chain).ok(),
                );
            }
            IbcEvent::TimeoutPacket(ref packet) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.packets.enabled,
                    || Object::for_timeout_packet(packet, src_chain).ok(),
                );
            }
            IbcEvent::WriteAcknowledgement(ref packet) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.packets.enabled,
                    || Object::for_write_ack(packet, src_chain).ok(),
                );
            }
            IbcEvent::CloseInitChannel(ref packet) => {
                collect_event(
                    &mut collected,
                    event_with_height.clone(),
                    mode.packets.enabled,
                    || Object::for_close_init_channel(packet, src_chain).ok(),
                );
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
    workers: &'a mut WorkerMap,
) -> SpawnContext<'a, Chain> {
    SpawnContext::new(config, registry, workers)
}

fn chain_scanner<'a, Chain: ChainHandle>(
    config: &'a Config,
    registry: &'a mut Registry<Chain>,
    client_state_filter: &'a mut FilterPolicy,
    full_scan: ScanMode,
) -> ChainScanner<'a, Chain> {
    ChainScanner::new(config, registry, client_state_filter, full_scan)
}

/// Perform a health check on all connected chains
fn health_check<Chain: ChainHandle>(config: &Config, registry: &mut Registry<Chain>) {
    use HealthCheck::*;

    let chains = &config.chains;

    for config in chains {
        let id = &config.id;
        let _span = error_span!("health_check", chain = %id).entered();

        let chain = registry.get_or_spawn(id);

        match chain {
            Ok(chain) => match chain.health_check() {
                Ok(Healthy) => info!("chain is healthy"),
                Ok(Unhealthy(e)) => warn!("chain is not healthy: {}", e),
                Err(e) => error!("failed to perform health check: {}", e),
            },
            Err(e) => {
                error!(
                    "skipping health check, reason: failed to spawn chain runtime with error: {}",
                    e
                );
            }
        }
    }
}

/// Subscribe to the events emitted by the chains the supervisor is connected to.
#[instrument(name = "supervisor.init_subscriptions", level = "error", skip_all)]
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
    SupervisorState::new(chains, workers.handles())
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

#[instrument(name = "supervisor.handle_rest_cmd", level = "error", skip_all)]
fn handle_rest_cmd<Chain: ChainHandle>(
    registry: &Registry<Chain>,
    workers: &WorkerMap,
    m: rest::Command,
) {
    match m {
        rest::Command::DumpState(reply) => {
            let state = state(registry, workers);
            reply
                .send(Ok(state))
                .unwrap_or_else(|e| error!("error replying to a REST request {}", e));
        }
    }
}

#[instrument(
    name = "supervisor.clear_pending_packets",
    level = "error",
    skip_all,
    fields(chain = %chain_id)
)]
fn clear_pending_packets(workers: &mut WorkerMap, chain_id: &ChainId) -> Result<(), Error> {
    for worker in workers.workers_for_chain(chain_id) {
        worker.clear_pending_packets();
    }

    Ok(())
}

/// Process a batch of events received from a chain.
#[instrument(
    name = "supervisor.process_batch",
    level = "error",
    skip_all,
    fields(chain = %src_chain.id()))
]
fn process_batch<Chain: ChainHandle>(
    config: &Config,
    registry: &mut Registry<Chain>,
    client_state_filter: &mut FilterPolicy,
    workers: &mut WorkerMap,
    src_chain: Chain,
    batch: &EventBatch,
) -> Result<(), Error> {
    assert_eq!(src_chain.id(), batch.chain_id);

    telemetry!(received_event_batch, batch.tracking_id);

    let collected = collect_events(config, workers, &src_chain, batch);

    // If there is a NewBlock event, forward this event first to any workers affected by it.
    if let Some(IbcEvent::NewBlock(new_block)) = collected.new_block {
        workers.notify_new_block(&src_chain.id(), batch.height, new_block);
    }

    // Forward the IBC events.
    for (object, events_with_heights) in collected.per_object.into_iter() {
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

        if events_with_heights.is_empty() {
            continue;
        }

        let src = registry
            .get_or_spawn(object.src_chain_id())
            .map_err(Error::spawn)?;

        let dst = registry
            .get_or_spawn(object.dst_chain_id())
            .map_err(Error::spawn)?;

        if let Object::Packet(ref _path) = object {
            // Update telemetry info
            telemetry!(send_telemetry(&src, &dst, &events_with_heights, _path));
        }

        let worker = workers.get_or_spawn(object, src, dst, config);

        worker.send_events(
            batch.height,
            events_with_heights,
            batch.chain_id.clone(),
            batch.tracking_id,
        );
    }

    Ok(())
}

/// This method parses a list of IbcEvent and record the following three metrics if there is
/// the corresponding event:
/// * send_packet_events: The number of SendPacket events received
/// * acknowledgement_events: The number of WriteAcknowledgment events received.
/// * timeout_events: The number of TimeoutPacket events received.
///
/// The labels `chain_id` represents the chain sending the event, and `counterparty_chain_id` represents
/// the chain receiving the event.
/// So successfully sending a packet from chain A to chain B will result in first a SendPacket
/// event with `chain_id = A` and `counterparty_chain_id = B` and then a WriteAcknowlegment
/// event with `chain_id = B` and `counterparty_chain_id = A`.
#[cfg(feature = "telemetry")]
fn send_telemetry<Src, Dst>(
    src: &Src,
    dst: &Dst,
    events: &[IbcEventWithHeight],
    path: &crate::object::Packet,
) where
    Src: ChainHandle,
    Dst: ChainHandle,
{
    telemetry! {
        for e in events {
            match e.event.clone() {
                IbcEvent::SendPacket(send_packet_ev) => {
                    ibc_telemetry::global().send_packet_events(
                        send_packet_ev.packet.sequence.into(),
                        e.height.revision_height(),
                        &src.id(),
                        &path.src_channel_id,
                        &path.src_port_id,
                        &dst.id(),
                    );
                }
                IbcEvent::WriteAcknowledgement(write_ack_ev) => {
                    ibc_telemetry::global().acknowledgement_events(
                        write_ack_ev.packet.sequence.into(),
                        e.height.revision_height(),
                        &src.id(),
                        &path.src_channel_id,
                        &path.src_port_id,
                        &dst.id(),
                    );
                }
                IbcEvent::TimeoutPacket(_) => {
                    ibc_telemetry::global().timeout_events(
                        &src.id(),
                        &path.src_channel_id,
                        &path.src_port_id,
                        &dst.id(),
                    );
                }
                _ => {}
            }
        }
    }
}

/// Process the given batch if it does not contain any errors,
/// output the errors on the console otherwise.
#[instrument(
    name = "supervisor.handle_batch",
    level = "error",
    skip_all,
    fields(chain = %chain.id())
)]
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
            if let Err(e) =
                process_batch(config, registry, client_state_filter, workers, chain, batch)
            {
                error!("error during batch processing: {}", e);
            }
        }
        Err(EventError(EventErrorDetail::SubscriptionCancelled(_), _)) => {
            warn!("event subscription was cancelled, clearing pending packets");

            let _ = clear_pending_packets(workers, &chain_id)
                .map_err(|e| error!("error during clearing pending packets: {}", e));
        }
        Err(e) => {
            error!("error when receiving event batch: {}", e)
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
    /// [`NewBlock`](ibc_relayer_types::events::IbcEventType::NewBlock) event
    /// collected from the [`EventBatch`].
    pub new_block: Option<IbcEvent>,
    /// Mapping between [`Object`]s and their associated [`IbcEvent`]s.
    pub per_object: HashMap<Object, Vec<IbcEventWithHeight>>,
    /// Unique identifier for tracking this event batch
    pub tracking_id: TrackingId,
}

impl CollectedEvents {
    pub fn new(height: Height, chain_id: ChainId, tracking_id: TrackingId) -> Self {
        Self {
            height,
            chain_id,
            tracking_id,
            new_block: Default::default(),
            per_object: Default::default(),
        }
    }

    /// Whether the collected events include a
    /// [`NewBlock`](ibc_relayer_types::events::IbcEventType::NewBlock) event.
    pub fn has_new_block(&self) -> bool {
        self.new_block.is_some()
    }
}
