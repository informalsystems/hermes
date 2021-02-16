extern crate stainless;
use stainless::*;

trait Clone {
    fn clone(&self) -> Self;
}
trait Default {
    fn default() -> Self;
}
pub trait Equals {
    fn eq(&self, other: &Self) -> bool;
}

pub enum Option<T> {
    Some(T),
    None,
}
impl<T> Option<T> {
    pub fn is_empty(&self) -> bool {
        match self {
            Option::Some(_) => true,
            _ => false,
        }
    }
}
impl<T: Clone> Clone for Option<T> {
    fn clone(&self) -> Self {
        match self {
            Option::Some(v) => Option::Some(v.clone()),
            Option::None => Option::None,
        }
    }
}
impl<T> Default for Option<T> {
    fn default() -> Option<T> {
        Option::None
    }
}

pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

impl<T> List<T> {
    pub fn is_empty(&self) -> bool {
        match self {
            List::Nil => true,
            _ => false,
        }
    }

    // These two consume the vec in order to invalidate it for further use
    fn push(self, x: T) -> Self {
        match self {
            List::Cons(head, tail) => List::Cons(head, Box::new(tail.push(x))),
            _ => List::Cons(x, Box::new(List::Nil)),
        }
    }

    fn append(self, other: List<T>) -> Self {
        match self {
            List::Cons(head, tail) => List::Cons(head, Box::new(tail.append(other))),
            _ => other,
        }
    }
}

impl List<Feature> {
    fn contains(&self, x: &Feature) -> bool {
        match self {
            List::Cons(y, tail) => x.eq(y) || tail.contains(x),
            _ => false,
        }
    }
}

impl<T: Clone> Clone for List<T> {
    fn clone(&self) -> Self {
        match self {
            List::Cons(h, tail) => List::Cons(h.clone(), Box::new((*tail).clone())),
            _ => List::Nil,
        }
    }
}

pub enum ErrorKind {
    InvalidPortCapability,
    NoPortCapability,
    InvalidVersion,
    ChannelFeatureNotSuportedByConnection,
    InvalidVersionLengthConnection,
    MissingConnection(ConnectionId),
    InvalidConnectionHopsLength,
}

// The following is all copied from various places in the ibc crate.
pub struct Height(u64);
impl Default for Height {
    fn default() -> Self {
        Height(1)
    }
}

pub struct AccountId(u64);

pub struct PortId(u64);
impl Clone for PortId {
    fn clone(&self) -> Self {
        PortId(self.0)
    }
}
impl Default for PortId {
    fn default() -> Self {
        let default_port: u64 = 1000;
        PortId(default_port)
    }
}
impl Equals for PortId {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

pub struct ChannelId(u64);
impl Clone for ChannelId {
    fn clone(&self) -> Self {
        ChannelId(self.0)
    }
}

pub struct ConnectionId(u64);
impl Default for ConnectionId {
    fn default() -> Self {
        let default_connection: u64 = 1000;
        ConnectionId(default_connection)
    }
}
impl Clone for ConnectionId {
    fn clone(&self) -> Self {
        ConnectionId(self.0)
    }
}
impl Equals for ConnectionId {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

pub struct ClientId(u64);

pub enum Feature {
    Order(Order),
}
impl Clone for Feature {
    fn clone(&self) -> Self {
        match self {
            Feature::Order(o) => Feature::Order(o.clone()),
        }
    }
}
impl Equals for Feature {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Feature::Order(o), Feature::Order(p)) => o.eq(p),
        }
    }
}

pub struct Version {
    /* unused
    /// unique version identifier
    identifier: String,
     */
    /// list of features compatible with the specified identifier
    features: List<Feature>,
}
impl Version {
    /// Checks whether or not the given feature is supported in this version
    pub fn is_supported_feature(&self, feature: Feature) -> bool {
        self.features.contains(&feature)
    }
}
impl Clone for Version {
    fn clone(&self) -> Self {
        Version {
            features: self.features.clone(),
        }
    }
}

pub struct Attributes {
    pub height: Height,
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub connection_id: ConnectionId,
    pub counterparty_port_id: PortId,
    pub counterparty_channel_id: Option<ChannelId>,
}

impl Default for Attributes {
    fn default() -> Self {
        Attributes {
            height: Default::default(),
            port_id: Default::default(),
            channel_id: Default::default(),
            connection_id: Default::default(),
            counterparty_port_id: Default::default(),
            counterparty_channel_id: Default::default(),
        }
    }
}

pub struct OpenInit(Attributes);

impl OpenInit {
    pub fn channel_id(&self) -> &Option<ChannelId> {
        &self.0.channel_id
    }
}

pub enum IBCEvent {
    OpenInitChannel(OpenInit),
    Other,
}

pub struct HandlerOutput<T> {
    pub result: T,
    pub log: List<Log>,
    pub events: List<IBCEvent>,
}

impl HandlerOutput<ChannelResult> {
    pub fn builder() -> HandlerOutputBuilder {
        HandlerOutputBuilder::new()
    }
}

pub enum Log {
    NoChannelFound,
}

pub struct HandlerOutputBuilder {
    log: List<Log>,
    events: List<IBCEvent>,
    // marker: PhantomData<T>,
}

impl HandlerOutputBuilder {
    pub fn new() -> Self {
        Self {
            log: List::Nil,
            events: List::Nil,
        }
    }

    pub fn with_log(self, log: List<Log>) -> Self {
        HandlerOutputBuilder {
            log: self.log.append(log),
            events: self.events,
        }
    }

    pub fn log(self, log: Log) -> Self {
        HandlerOutputBuilder {
            log: self.log.push(log),
            events: self.events,
        }
    }

    pub fn with_events(self, events: List<IBCEvent>) -> Self {
        HandlerOutputBuilder {
            events: self.events.append(events),
            log: self.log,
        }
    }

    pub fn emit(self, event: IBCEvent) -> Self {
        HandlerOutputBuilder {
            events: self.events.push(event),
            log: self.log,
        }
    }

    pub fn with_result(self, result: ChannelResult) -> HandlerOutput<ChannelResult> {
        HandlerOutput {
            result,
            log: self.log,
            events: self.events,
        }
    }
}

pub struct VersionId(u64);
impl Clone for VersionId {
    fn clone(&self) -> Self {
        VersionId(self.0)
    }
}

#[allow(dead_code)]
pub struct ChannelEnd {
    state: State,
    ordering: Order,
    remote: Counterparty,
    connection_hops: List<ConnectionId>,
    version: Option<VersionId>,
}

impl ChannelEnd {
    pub fn new(
        state: State,
        ordering: Order,
        remote: Counterparty,
        connection_hops: List<ConnectionId>,
        version: Option<VersionId>,
    ) -> Self {
        Self {
            state,
            ordering,
            remote,
            connection_hops,
            version,
        }
    }

    pub fn ordering(&self) -> &Order {
        &self.ordering
    }

    pub fn counterparty(&self) -> &Counterparty {
        &self.remote
    }

    pub fn connection_hops(&self) -> &List<ConnectionId> {
        &self.connection_hops
    }

    pub fn version(&self) -> &Option<VersionId> {
        &self.version
    }
}

pub enum Order {
    None = 0,
    Unordered,
    Ordered,
}
impl Order {
    pub fn as_feature(&self) -> Feature {
        Feature::Order(self.clone())
    }
}
impl Clone for Order {
    fn clone(&self) -> Self {
        match self {
            Order::None => Order::None,
            Order::Unordered => Order::Unordered,
            Order::Ordered => Order::Ordered,
        }
    }
}
impl Equals for Order {
    fn eq(&self, other: &Order) -> bool {
        match (self, other) {
            (Order::None, Order::None) => true,
            (Order::Unordered, Order::Unordered) => true,
            (Order::Ordered, Order::Ordered) => true,
            _ => false,
        }
    }
}

pub struct Counterparty {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
}

impl Clone for Counterparty {
    fn clone(&self) -> Self {
        Counterparty {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
        }
    }
}

pub enum State {
    Uninitialized = 0,
    Init = 1,
    TryOpen = 2,
    Open = 3,
    Closed = 4,
}

pub struct ChannelResult {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub channel_cap: Capability,
    pub channel_end: ChannelEnd,
}

pub struct Capability {
    _index: u64,
}
impl Clone for Capability {
    fn clone(&self) -> Self {
        Capability {
            _index: self._index,
        }
    }
}
impl Equals for Capability {
    fn eq(&self, other: &Self) -> bool {
        self._index == other._index
    }
}

pub struct ConnectionEnd {
    // unused state: State,
    // unused client_id: ClientId,
    // unused counterparty: Counterparty,
    versions: List<Version>,
    // unused pub(crate) delay_period: u64,
}
impl Clone for ConnectionEnd {
    fn clone(&self) -> Self {
        ConnectionEnd {
            versions: self.versions.clone(),
        }
    }
}

pub struct MsgChannelOpenInit {
    pub port_id: PortId,
    pub channel: ChannelEnd,
    pub signer: AccountId,
}

impl MsgChannelOpenInit {
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn channel(&self) -> &ChannelEnd {
        &self.channel
    }
}

pub trait ChannelReader {
    /// Returns the ConnectionState for the given identifier `connection_id`.
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<ConnectionEnd>;

    fn port_capability(&self, port_id: &PortId) -> Option<Capability>;

    fn capability_authentification(&self, port_id: &PortId, cap: &Capability) -> bool;
}

pub struct MockChannelReader {
    connection_id: ConnectionId,
    connection_end: ConnectionEnd,
    port_id: PortId,
    cap: Capability,
}

impl ChannelReader for MockChannelReader {
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<ConnectionEnd> {
        if connection_id.eq(&self.connection_id) {
            Option::Some(self.connection_end.clone())
        } else {
            Option::None
        }
    }

    fn port_capability(&self, port_id: &PortId) -> Option<Capability> {
        if port_id.eq(&self.port_id) {
            Option::Some(self.cap.clone())
        } else {
            Option::None
        }
    }

    fn capability_authentification(&self, port_id: &PortId, cap: &Capability) -> bool {
        port_id.eq(&self.port_id) && cap.eq(&self.cap)
    }
}

/// The actual function we want to verify
pub fn process(
    ctx: MockChannelReader,
    msg: MsgChannelOpenInit,
) -> Result<HandlerOutput<ChannelResult>, ErrorKind> {
    let output = HandlerOutput::builder();

    match ctx.port_capability(&msg.port_id().clone()) {
        Option::None => Result::Err(ErrorKind::NoPortCapability),

        Option::Some(key) => {
            if !ctx.capability_authentification(&msg.port_id().clone(), &key) {
                Result::Err(ErrorKind::InvalidPortCapability)
            }
            // An IBC connection running on the local (host) chain should exist.
            else {
                match msg.channel().connection_hops() {
                    List::Cons(hop, tail) if tail.is_empty() => {
                        match ctx.connection_end(hop) {
                            Option::None => Result::Err(ErrorKind::MissingConnection(hop.clone())),

                            Option::Some(conn) => {
                                match conn.versions {
                                    List::Cons(version, tail) if tail.is_empty() => {
                                        let channel_feature = msg.channel().ordering().as_feature();
                                        if !version.is_supported_feature(channel_feature) {
                                            Result::Err(
                                                ErrorKind::ChannelFeatureNotSuportedByConnection,
                                            )
                                        }
                                        // TODO: Check that `version` is non empty but not necessary coherent
                                        else if msg.channel().version().is_empty() {
                                            Result::Err(ErrorKind::InvalidVersion)
                                        } else {
                                            let new_channel_end = ChannelEnd::new(
                                                State::Init,
                                                msg.channel().ordering().clone(),
                                                msg.channel().counterparty().clone(),
                                                msg.channel().connection_hops().clone(),
                                                msg.channel().version().clone(),
                                            );

                                            let output = output.log(Log::NoChannelFound);

                                            let result = ChannelResult {
                                                port_id: msg.port_id().clone(),
                                                channel_id: Option::None,
                                                channel_end: new_channel_end,
                                                channel_cap: key,
                                            };

                                            let default_attributes: Attributes = Default::default();
                                            let event_attributes = Attributes {
                                                channel_id: Option::None,
                                                height: default_attributes.height,
                                                port_id: default_attributes.port_id,
                                                connection_id: default_attributes.connection_id,
                                                counterparty_port_id: default_attributes
                                                    .counterparty_port_id,
                                                counterparty_channel_id: default_attributes
                                                    .counterparty_channel_id,
                                            };
                                            let output = output.emit(IBCEvent::OpenInitChannel(
                                                OpenInit(event_attributes),
                                            ));

                                            Result::Ok(output.with_result(result))
                                        }
                                    }
                                    _ => Result::Err(ErrorKind::InvalidVersionLengthConnection),
                                }
                            }
                        }
                    }
                    _ => Result::Err(ErrorKind::InvalidConnectionHopsLength),
                }
            }
        }
    }
}

pub fn main() {}
