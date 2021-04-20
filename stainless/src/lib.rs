extern crate stainless;
use stainless::*;

use std::marker::PhantomData;

trait Default {
    fn default() -> Self;
}
pub trait Equals {
    fn eq(&self, other: &Self) -> bool;
}

impl Equals for String {
    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

pub enum Option<T> {
    Some(T),
    None,
}
impl<T> Default for Option<T> {
    fn default() -> Option<T> {
        Option::None
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

pub enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

impl<T> List<T> {
    fn len(&self) -> usize {
        match self {
            List::Cons(_, tail) => 1 + tail.len(),
            _ => 0,
        }
    }

    fn first(&self) -> Option<&T> {
        match self {
            List::Cons(v, _) => Option::Some(&v),
            _ => Option::None,
        }
    }

    fn push(self, x: T) -> Self {
        match self {
            List::Cons(head, tail) => List::Cons(head, Box::new(tail.push(x))),
            _ => List::Cons(x, Box::new(List::Nil)),
        }
    }
}

impl<T: Equals> List<T> {
    fn contains(&self, x: &T) -> bool {
        match self {
            List::Cons(y, tail) => x.eq(y) || tail.contains(x),
            _ => false,
        }
    }
}

impl<T: Clone> Clone for List<T> {
    fn clone(&self) -> Self {
        match self {
            List::Cons(h, tail) => List::Cons(h.clone(), Box::new((**tail).clone())),
            _ => List::Nil,
        }
    }
}

pub struct ChannelId(u64);
impl ChannelId {
    pub fn new(counter: u64) -> Self {
        ChannelId(counter)
    }
}
impl Default for ChannelId {
    fn default() -> Self {
        Self::new(0)
    }
}
impl Clone for ChannelId {
    fn clone(&self) -> Self {
        ChannelId(self.0)
    }
}

pub struct PortId(String);
impl Clone for PortId {
    fn clone(&self) -> Self {
        PortId(self.0.clone())
    }
}
impl Default for PortId {
    fn default() -> Self {
        PortId("defaultPort".to_string())
    }
}
impl Equals for PortId {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

pub struct ConnectionId(u64);
impl ConnectionId {
    pub fn new(counter: u64) -> Self {
        ConnectionId(counter)
    }
}
impl Default for ConnectionId {
    fn default() -> Self {
        Self::new(0)
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

pub struct ClientId(String);

pub struct Height {
    pub revision_number: u64,
    pub revision_height: u64,
}

impl Default for Height {
    fn default() -> Self {
        Height {
            revision_height: 0,
            revision_number: 0,
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

pub enum State {
    Uninitialized = 0,
    Init = 1,
    TryOpen = 2,
    Open = 3,
    Closed = 4,
}
impl Equals for State {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (State::Uninitialized, State::Uninitialized) => true,
            (State::Init, State::Init) => true,
            (State::TryOpen, State::TryOpen) => true,
            (State::Open, State::Open) => true,
            (State::Closed, State::Closed) => true,
            _ => false,
        }
    }
}

pub enum ChannelIdState {
    Generated,
    Reused,
}

pub enum Order {
    None = 0,
    Unordered,
    Ordered,
}

impl Order {
    /// Yields the Order as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::None => "UNINITIALIZED",
            Self::Unordered => "ORDER_UNORDERED",
            Self::Ordered => "ORDER_ORDERED",
        }
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

pub struct ChannelEnd {
    pub state: State,
    pub ordering: Order,
    pub remote: Counterparty,
    pub connection_hops: List<ConnectionId>,
    pub version: String,
}

impl ChannelEnd {
    pub fn connection_hops(&self) -> &List<ConnectionId> {
        &self.connection_hops
    }
    pub fn ordering(&self) -> &Order {
        &self.ordering
    }
    pub fn counterparty(&self) -> &Counterparty {
        &self.remote
    }
    pub fn version(&self) -> String {
        self.version.clone()
    }
}

pub struct Version {
    /// unique version identifier
    // identifier: String,
    /// list of features compatible with the specified identifier
    features: List<String>,
}

impl Version {
    /// Checks whether or not the given feature is supported in this versin
    pub fn is_supported_feature(&self, feature: String) -> bool {
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

pub struct ConnectionEnd {
    // state: State,
    // client_id: ClientId,
    // counterparty: Counterparty,
    versions: List<Version>,
    // delay_period: u64,
}

impl ConnectionEnd {
    pub fn versions(&self) -> &List<Version> {
        &self.versions
    }
}
impl Clone for ConnectionEnd {
    fn clone(&self) -> Self {
        ConnectionEnd {
            versions: self.versions.clone(),
        }
    }
}

pub struct OpenInit(Attributes);

pub enum IbcEvent {
    OpenInitChannel(OpenInit),
}

pub struct HandlerOutput<T> {
    pub result: T,
    pub log: List<String>,
    pub events: List<IbcEvent>,
}

impl<T> HandlerOutput<T> {
    pub fn builder() -> HandlerOutputBuilder<T> {
        HandlerOutputBuilder::new()
    }
}

pub struct HandlerOutputBuilder<T> {
    log: List<String>,
    events: List<IbcEvent>,
    marker: PhantomData<T>,
}

impl<T> HandlerOutputBuilder<T> {
    pub fn new() -> Self {
        Self {
            log: List::Nil,
            events: List::Nil,
            marker: PhantomData,
        }
    }

    pub fn log(self, log: String) -> Self {
        HandlerOutputBuilder {
            log: self.log.push(log),
            ..self
        }
    }

    pub fn emit(self, event: IbcEvent) -> Self {
        HandlerOutputBuilder {
            events: self.events.push(event),
            ..self
        }
    }

    pub fn with_result(self, result: T) -> HandlerOutput<T> {
        HandlerOutput {
            result,
            log: self.log,
            events: self.events,
        }
    }
}

pub enum ErrorKind {
    InvalidConnectionHopsLength(usize, usize),
    MissingConnection(ConnectionId),
    InvalidVersionLengthConnection,
    ChannelFeatureNotSuportedByConnection,
    InvalidVersion,
    NoPortCapability(PortId),
}

#[allow(dead_code)]
pub struct Capability {
    index: u64,
}
impl Clone for Capability {
    fn clone(&self) -> Self {
        Capability { index: self.index }
    }
}

pub trait ChannelReader {
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<&ConnectionEnd>;

    fn authenticated_capability(&self, port_id: &PortId) -> Result<Capability, ErrorKind>;

    fn channel_counter(&self) -> u64;
}

pub struct MockChannelReader {
    connection_id: ConnectionId,
    connection_end: ConnectionEnd,
    port_id: PortId,
    cap: Capability,
}

impl ChannelReader for MockChannelReader {
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<&ConnectionEnd> {
        if connection_id.eq(&self.connection_id) {
            Option::Some(&self.connection_end)
        } else {
            Option::None
        }
    }

    fn channel_counter(&self) -> u64 {
        1
    }

    fn authenticated_capability(&self, port_id: &PortId) -> Result<Capability, ErrorKind> {
        if port_id.eq(&self.port_id) {
            Ok(self.cap.clone())
        } else {
            Err(ErrorKind::NoPortCapability(port_id.clone()))
        }
    }
}

pub struct Signer(String);

pub struct MsgChannelOpenInit {
    pub port_id: PortId,
    pub channel: ChannelEnd,
    pub signer: Signer,
}

impl MsgChannelOpenInit {
    /// Getter: borrow the `port_id` from this message.
    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    /// Getter: borrow the `channelEnd` from this message.
    pub fn channel(&self) -> &ChannelEnd {
        &self.channel
    }
}

pub struct ChannelResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub channel_id_state: ChannelIdState,
    pub channel_cap: Capability,
    pub channel_end: ChannelEnd,
}

#[post(
    (msg.channel().connection_hops().len() == 1
        && matches!(
            msg.channel().connection_hops().first(),
            Option::Some(f) if f.eq(&ctx.connection_id)
        )
        && msg.port_id().eq(&ctx.port_id)
        && ctx.connection_end.versions.len() == 1
        && matches!(
            ctx.connection_end.versions.first(),
            Option::Some(v) if v.is_supported_feature(
                msg.channel().ordering().as_string().to_string()
            )
        )
        && !msg.channel().version.is_empty())
    .implies(match &ret {
        Ok(output) => {
            output.result.channel_end.state.eq(&State::Init)
                && matches!(
                  (output.result.channel_end.connection_hops().first(),
                    msg.channel().connection_hops().first()),
                  (Option::Some(o), Option::Some(m)) if o.eq(m)
                )
        }
        _ => false,
    })
    && msg.channel().version.is_empty().implies(
        matches!(&ret, Err(_))
    )
)]

pub fn process(
    ctx: MockChannelReader,
    msg: MsgChannelOpenInit,
) -> Result<HandlerOutput<ChannelResult>, ErrorKind> {
    let output = HandlerOutput::builder();

    // Channel capabilities
    let channel_cap = match ctx.authenticated_capability(&msg.port_id()) {
        Ok(c) => c,
        Err(e) => return Err(e),
    };

    let hop = match msg.channel().connection_hops() {
        List::Cons(hop, tail) if tail.len() == 0 => hop,
        _ => {
            return Err(ErrorKind::InvalidConnectionHopsLength(
                1,
                msg.channel().connection_hops().len(),
            )
            .into())
        }
    };

    // An IBC connection running on the local (host) chain should exist.
    let conn = match ctx.connection_end(hop) {
        Option::Some(v) => v,
        _ => return Result::Err(ErrorKind::MissingConnection(hop.clone())),
    };

    let version = match conn.versions() {
        List::Cons(version, tail) if tail.len() == 0 => version,
        _ => return Result::Err(ErrorKind::InvalidVersionLengthConnection.into()),
    };

    let channel_feature = msg.channel().ordering().as_string().to_string();
    if !version.is_supported_feature(channel_feature) {
        return Err(ErrorKind::ChannelFeatureNotSuportedByConnection.into());
    }

    // TODO: Check that `version` is non empty but not necessary coherent
    if msg.channel().version.is_empty() {
        return Err(ErrorKind::InvalidVersion.into());
    }

    // Channel identifier construction.
    let id_counter = ctx.channel_counter();
    let chan_id = ChannelId::new(id_counter);

    let output = output.log("success: generated new channel identifier: {}".to_string());

    let new_channel_end = ChannelEnd {
        state: State::Init,
        ordering: msg.channel().ordering().clone(),
        remote: msg.channel().counterparty().clone(),
        connection_hops: msg.channel().connection_hops().clone(),
        version: msg.channel().version(),
    };

    let output = output.log("success: no channel found".to_string());

    let result = ChannelResult {
        port_id: msg.port_id().clone(),
        channel_id: chan_id.clone(),
        channel_end: new_channel_end,
        channel_id_state: ChannelIdState::Generated,
        channel_cap,
    };

    let event_attributes = Attributes {
        channel_id: Option::Some(chan_id),
        ..Default::default()
    };
    let output = output.emit(IbcEvent::OpenInitChannel(OpenInit(event_attributes)));

    Ok(output.with_result(result))
}
