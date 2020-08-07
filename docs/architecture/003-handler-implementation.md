# ADR 003: Handler implementation

## Changelog
* 2020-08-06: Initial proposal

## Context

> This section contains all the context one needs to understand the current state, and why there is a problem. It should be as succinct as possible and introduce the high level idea behind the solution.

TODO

## Decision

In this chapter, we provide recommendation for implementing IBC handlers within the `ibc-rs` crate.
Concepts are introduced in the order given by a topological sort of their dependencies on each other.

### Events

IBC handlers must be able to emit events which will then be broadcasted via the node's pub/sub mechanism,
and eventually picked up by the IBC relayer.

A generic interface for events is provided below, where an event is represented
as a pair of an event type and a list of attributes. An attribute is simply a pair
of a key and a value, both represented as strings. TODO: Describe event type.

```rust
pub struct Attribute {
    key: String,
    value: String,
}

impl Attribute {
    pub fn new(key: String, value: String) -> Self;
}

pub enum EventType {
    Message,
    Custom(String),
}

pub struct Event {
    tpe: EventType,
    attributes: Vec<Attribute>,
}

impl Event {
    pub fn new(tpe: EventType, attrs: Vec<(String, String)>) -> Self;
}
```

### Logging

IBC handlers must be able to log information for introspectability and ease of debugging.
A handler can output multiple log records, which are expressed as a pair of a status and a
log line. The interface for emitting log records is described in the next section.

```rust
pub enum LogStatus {
  Success,
  Info,
  Warning,
  Error,
}

pub struct Log {
  status: LogStatus,
  body: String,
}

impl Log {
  fn success(msg: impl Display) -> Self;
  fn info(msg: impl Display) -> Self;
  fn warning(msg: impl Display) -> Self;
  fn error(msg: impl Display) -> Self;
}
```

### Handler output

IBC handlers must be able to return arbitrary data, together with events and log records, as descibed above.
As a handler may fail, it is necessary to keep track of errors.

To this end, we introduce a type for the return value of a handler:

```rust
pub type HandlerResult<T, E> = Result<HandlerOutput<T>, E>;

pub struct HandlerOutput<T> {
    pub result: T,
    pub log: Vec<Log>,
    pub events: Vec<Event>,
}
```

We introduce a builder interface to be used within the handler implementation to incrementally build a `HandlerOutput` value.

```rust
impl<T> HandlerOutput<T> {
    pub fn builder() -> HandlerOutputBuilder<T> {
        HandlerOutputBuilder::new()
    }
}

pub struct HandlerOutputBuilder<T> {
    log: Vec<String>,
    events: Vec<Event>,
    marker: PhantomData<T>,
}

impl<T> HandlerOutputBuilder<T> {
    pub fn log(&mut self, log: impl Into<Log>);
    pub fn emit(&mut self, event: impl Into<Event>);
    pub fn with_result(self, result: T) -> HandlerOutput<T>;
}
```

We provide below an example usage of the builder API:

```rust
fn some_ibc_handler() -> HandlerResult<u64, Error> {
  let mut output = HandlerOutput::builder();

  // ...

  output.log(Log::info("did something"))

  // ...

  output.log(Log::success("all good"));
  output.emit(SomeEvent::AllGood);

  Ok(output.with_result(42));
}
```

### IBC Submodule

The various IBC messages and their handlers, as described in the IBC specification,
are split into a collection of submodules, each pertaining to a specific aspect of
the IBC protocol, eg. client lifecycle management, connection lifecycle management,
packet relay, etc.

In this section we propose a general approach to implement the handlers for a submodule.
To make things more concrete, we will use the ICS 002 Client submodule as a
running example, but the methodology outlined here should apply to any submodule.
This specific module also has the peculiarity of dealing with datatypes which
are specific to a given type of chain, eg. Tendermint. This incurs the need for
abstracting over these datatypes, which introduces additional abstractions which
may not be needed for other submodules.

#### Events

The events which may be emitted by the handlers of a submodule should be defined
as an enumeration, while a way of converting those into the generic `Event` type
defined in a previous section should be provided via the `From` trait.

We provide below an implementation of both for the ICS 002 Client submodule:

```rust
pub enum ClientEvent {
    ClientCreated(ClientId),
    ClientUpdated(ClientId),
}

impl From<ClientEvent> for Event {
    fn from(ce: ClientEvent) -> Event {
        match ce {
            ClientEvent::ClientCreated(client_id) => Event::new(
                EventType::Custom("ClientCreated".to_string()),
                vec![("client_id".to_string(), client_id.to_string())],
            ),
            ClientEvent::ClientUpdated(client_id) => Event::new(
                EventType::Custom("ClientUpdated".to_string()),
                vec![("client_id".to_string(), client_id.to_string())],
            ),
        }
    }
}
```

#### Abstracting over chain-specific datatypes

To abstract over chain-specific datatypes, we introduce a trait which specifies
both which types we need to abstract over and their interface. For the Client submodule,
this trait looks as follow:

```rust
pub trait ClientDef {
    type Header: Header;
    type ClientState: ClientState + From<Self::ConsensusState>;
    type ConsensusState: ConsensusState;
}
```

This trait specifies three datatypes, and their corresponding interface, which is provided
via a trait defined in the same submodule.
Additionally, this trait expresses the requirement for a `ClientState` to be built from
a `ConsensusState`.

A production implementation of this interface would instantiate these types with the concrete
types used by the chain.

For the purpose of unit-testing, a mock implementation of the `ClientDef` trait could look as
follows:

```rust
struct MockHeader(u32);
impl Header for MockHeader {
  // omitted
}

struct MockClientState(u32);
impl ClientState for MockClientState {
  // omitted
}

impl From<MockConsensusState> for MockClientState {
    fn from(cs: MockConsensusState) -> Self {
        Self(cs.0)
    }
}

struct MockConsensusState(u32);
impl ConsensusState for MockConsensusState {
  // omitted
}

struct MockClient;

impl ClientDef for MockClient {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;
}
```

#### Reader

A typical handler will need to read data from the chain state at the current height,
via the private and provable stores.

To avoid coupling between the handler interface and the store API, we introduce an interface
for accessing this data. This interface is shared between all handlers in a submodule, as
those typically access the same data.

Having a high-level interface for this purpose helps avoiding coupling which makes
writing unit tests for the handlers easier, as one does not need to provide a concrete
store, or to mock one.

We provide below the definition of such an interface, called a `Reader` for the ICS 02 Client submodule:

```rust
pub trait ClientReader<CD>
where
    CD: ClientDef,
{
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: &ClientId) -> Option<CD::ClientState>;
    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<CD::ConsensusState>;
}
```

Because the data exposed by this `Reader` is chain-specific, the `Reader` trait is parametrized
by the type of chain, via the `ClientDef` trait bound. Other submodules may not need the generality
and do away with the type parameter and trait bound altogether.

A production implementation of this `Reader` would hold references to both the private and provable
store at the current height where the handler executes, but we omit the actual implementation as
the store interfaces are yet to be defined, as is the general IBC top-level module machinery.

A mock implementation of the `ClientReader` trait could look as follows, given the `MockClient`
definition provided in the previous section.

```rust
struct MockClientContext {
    client_id: ClientId,
    client_state: Option<MockClientState>,
    client_type: Option<ClientType>,
    consensus_state: Option<MockConsensusState>,
}

impl ClientContext<MockClient> for MockClientContext {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        if client_id == &self.client_id {
            self.client_type.clone()
        } else {
            None
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Option<MockClientState> {
        if client_id == &self.client_id {
            self.client_state
        } else {
            None
        }
    }

    fn consensus_state(&self, client_id: &ClientId, _height: Height) -> Option<MockConsensusState> {
        if client_id == &self.client_id {
            self.consensus_state
        } else {
            None
        }
    }
}
```

#### Keeper

Once a handler executes successfully, some data will typically need to be persisted in the chain state
via the private/provable store interfaces. In the same vein as for the reader defined in the previous section,
a submodule should define a trait which provides operations to persist such data.
The same considerations w.r.t. to coupling and unit-testing apply here as well.

We give below a version of this keeper trait for the Client submodule:

```rust
pub trait ClientKeeper<CD: ClientDef> {
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Error>;

    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: CD::ClientState,
    ) -> Result<(), Error>;

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        consensus_state: CD::ConsensusState,
    ) -> Result<(), Error>;
}
```

Other submodules may not need the generality and do away with the type parameter and trait
bound altogether.

#### Handler implementation

We now come to the actual definition of a handler for a submodule.

We recommend each handler to be defined within its own Rust module, named
after the handler itself. For example, the "Create Client" handler of ICS 002 would
be defined in `ibc_modules::ics02_client::handler::create_client`.

##### Message type

Each handler must define a datatype which represent the message it can process.
For the "Create Client" handler of ICS 002, the message would look as follows:

```rust
pub struct MsgCreateClient<C: ClientDef> {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub consensus_state: C::ConsensusState,
}
```

Again, because the message mentions chain-specific datatypes, it must be parametrized by
the type of chain, bounded by the `ClientDef` trait defined in an earlier section.
Other submodules may not need the generality and do away with the type parameter and trait
bound altogether.

##### Handler implementation

In this section we provide guidelines for implementating an actual handler.

We divide the handler in two parts: processing and persistance.

###### Processing

The actual logic of the handler is expressed as a pure function, typically named
`process`, which takes as arguments a `Reader` and the corresponding message, and returns
a `HandlerOutput<T, E>`, where `T` is a concrete datatype and `E` is an error type which defines
all potential errors yielded by the handlers of the current submodule.

For the "Create Client" handler of ICS 002, `T` would be defined as the following datatype:

```rust
pub struct CreateClientResult<CD: ClientDef> {
    client_id: ClientId,
    client_type: ClientType,
    client_state: CD::ClientState,
}
```

The `process` function will typically read data via the `Reader`, perform checks and validation, construct new
datatypes, emit log records and events, and eventually return some data together with objects to be persisted.

To this end, this `process` function will create and manipulate a `HandlerOutput` value like described in
the corresponding section.

We provide below the actual implementation of the `process` function for the "Create Client" handler of ICS 002:

```rust
pub fn process<CD>(
    reader: &dyn ClientReader<CD>,
    msg: MsgCreateClient<CD>,
) -> HandlerResult<CreateClientResult<CD>, Error>
where
    CD: ClientDef,
{
    let mut output = HandlerOutput::builder();

    let MsgCreateClient {
        client_id,
        client_type,
        consensus_state,
    } = msg;

    if reader.client_state(&client_id).is_some() {
        return Err(Kind::ClientAlreadyExists(client_id).into());
    }

    output.log("success: no client state found");

    if reader.client_type(&client_id).is_some() {
        return Err(Kind::ClientAlreadyExists(client_id).into());
    }

    output.log("success: no client type found");

    let client_state = consensus_state.into();

    output.emit(ClientEvent::ClientCreated(client_id.clone()));

    Ok(output.with_result(CreateClientResult {
        client_id,
        client_type,
        client_state,
    }))
}
```

Again, because this handler deals with chain-specific data, the `process` function is parametrized
by the type of chain, via the `ClientDef` trait bound. Other submodules or handlers may not need the generality
and do away with the type parameter and trait bound altogether.

###### Persistence

If the `process` function specified above succeeds, the result value it yielded is then
passed to a function named `keep`, which is responsible for persisting the objects constructed
by the processing function. This `keep` function takes the submodule's `Keeper` and the result
type defined above, and performs side-effecting calls to the keeper's methods to persist the result.

Below is given an implementation of the `keep` function for the "Create Client" handler:

```rust
pub fn keep<CD>(
    keeper: &mut dyn ClientKeeper<CD>,
    result: CreateClientResult<CD>,
) -> Result<(), Error>
where
    CD: ClientDef,
{
    keeper.store_client_state(result.client_id.clone(), result.client_state)?;
    keeper.store_client_type(result.client_id, result.client_type)?;

    Ok(())
}
```

##### Submodule handler

> This section is very much a work in progress, as further investigation into what
> a production-ready implementation of the `ctx` parameter of the top-level handler
> is required. As such, implementors should feel free to disregard the recommendations
> below, and are encouraged to come up with amendments to this ADR to better capture
> the actual requirements.

Each submodule is responsible for dispatching the messages it is given to the appropriate
handler processing function and, if successful, pass the resulting data to the persistance
function defined in the previous section.

To this end, the submodule should define an enumeration of all handlers messages, in order
for the top-level submodule handler to dispatch them. Such a definition for the ICS 002 Client
submodule is given below.

```rust
pub enum ClientMsg<CD: ClientDef> {
    CreateClient(MsgCreateClient<CD>),
    UpdateClient(UpdateClientMsg<CD>),
}
```

Because the messages mention chain-specific datatypes, the whole enumeration must be parametrized by
the type of chain, bounded by the `ClientDef` trait defined in an earlier section.
Other submodules may not need the generality and do away with the type parameter and trait
bound altogether.

The actual implementation of a submodule handler is quite straightforward and unlikely to vary
much in substance between submodules. We give an implementation for the ICS 002 Client module below.

```rust
pub fn handler<Client, Ctx>(ctx: &mut Ctx, msg: ClientMsg<Client>) -> Result<HandlerOutput<()>, Error>
where
    Client: ClientDef,
    Ctx: ClientContext<Client> + ClientKeeper<Client>,
{
    match msg {
        ClientMsg::CreateClient(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = create_client::process(ctx, msg)?;

            create_client::keep(ctx, result)?;

            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(()))
        }

        ClientMsg::UpdateClient(msg) => // omitted
    }
}
```

In essence, a top-level handler is a function of a message wrapped in the enumeration introduced above,
and a "context" which implements both the `Reader` and `Keeper` interfaces.

It is currently not clear if such a requirement is actually viable, as handlers might need to access
a `Keeper` for various chain types known only at runtime, which would prevent having a static bound
on the context, as expressed above. Further investigations are required to sort this out, hence the
disclaimer at the beginning of this section.

## Status

Proposed

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive

### Negative

### Neutral

## References

> Are there any relevant PR comments, issues that led up to this, or articles refernced for why we made the given design choice? If so link them here!

* {reference link}
