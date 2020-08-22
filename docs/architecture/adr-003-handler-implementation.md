# ADR 003: IBC protocol implementation

## Changelog
* 2020-08-06: Initial proposal
* 2020-08-10: Rename Handler to Message Processor
* 2020-08-14: Revamp definition of chain-specific messages, readers and keepers

## Reader

> This section contains all the context one needs to understand the current state, and why there is a problem. It should be as succinct as possible and introduce the high level idea behind the solution.

TODO

## Decision

In this ADR, we provide recommendations for implementing the IBC message processing logic within the `ibc-rs` crate.
Concepts are introduced in the order given by a topological sort of their dependencies on each other.

### Events

IBC message processors must be able to emit events which will then be broadcasted via the node's pub/sub mechanism,
and eventually picked up by the IBC relayer.

A generic interface for events is provided below, where an event is represented
as a pair of an event type and a list of attributes. An attribute is simply a pair
of a key and a value, both represented as strings.

Here is the [list of all IBB-related events][events], as seen by the relayer.
Because the structure of these events do not match the ones which are emitted by the IBC message processors,
each IBC submodule should defined its own event type and associated variants.

[events]: https://github.com/informalsystems/ibc-rs/blob/bf84a73ef7b3d5e9a434c9af96165997382dcc9d/modules/src/events.rs#L15-L43

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
    typ: EventType,
    attributes: Vec<Attribute>,
}

impl Event {
    pub fn new(typ: EventType, attrs: Vec<(String, String)>) -> Self;
}
```

### Logging

IBC message processors must be able to log information for introspectability and ease of debugging.
A message processor can output multiple log records, which are expressed as a pair of a status and a
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

### Message processor output

IBC message processors must be able to return arbitrary data, together with events and log records, as descibed above.
As a message processor may fail, it is necessary to keep track of errors.

To this end, we introduce a type for the return value of a message processor:

```rust
pub type HandlerResult<T, E> = Result<HandlerOutput<T>, E>;

pub struct HandlerOutput<T> {
    pub result: T,
    pub log: Vec<Log>,
    pub events: Vec<Event>,
}
```

We introduce a builder interface to be used within the message processor implementation to incrementally build a `HandlerOutput` value.

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

The various IBC messages and their processing logic, as described in the IBC specification,
are split into a collection of submodules, each pertaining to a specific aspect of
the IBC protocol, eg. client lifecycle management, connection lifecycle management,
packet relay, etc.

In this section we propose a general approach to implement the message processors for a submodule.
As a running example we will use a dummy submodule that deals with connections, which should not
be mistaken for the actual ICS 003 Connection submodule.

#### Events

The events which may be emitted by the message processors of a submodule should be defined
as an enumeration, while a way of converting those into the generic `Event` type
defined in a previous section should be provided via the `From` trait.

```rust
pub enum ConnectionEvent {
    ConnectionOpenInit(ConnectionId),
    ConnectionOpenTry(ConnectionId),
}

impl From<ConnectionEvent> for Event {
    fn from(ce: ConnectionEvent) -> Event {
        match ce {
            ConnectionEvent::ConnectionOpenInit(connection_id) => Event::new(
                EventType::Custom("ConnectionOpenInit".to_string()),
                vec![("connection_id".to_string(), connection_id.to_string())],
            ),
            ConnectionEvent::ConnectionOpenTry(connection_id) => Event::new(
                EventType::Custom("ConnectionOpenTry".to_string()),
                vec![("connection_id".to_string(), connection_id.to_string())],
            ),
        }
    }
}
```

#### Reader

A typical message processor will need to read data from the chain state at the current height,
via the private and provable stores.

To avoid coupling between the message processor interface and the store API, we introduce an interface
for accessing this data. This interface, called a `Reader`, is shared between all message processors
in a submodule, as those typically access the same data.

Having a high-level interface for this purpose helps avoiding coupling which makes
writing unit tests for the message processors easier, as one does not need to provide a concrete
store, or to mock one.

```rust
pub trait ConnectionReader
{
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<ConnectionEnd>;
}
```

A production implementation of this `Reader` would hold references to both the private and provable
store at the current height where the message processor executes, but we omit the actual implementation as
the store interfaces are yet to be defined, as is the general IBC top-level module machinery.

A mock implementation of the `ConnectionReader` trait could look as follows:

```rust
struct MockConnectionReader {
    connection_id: ConnectionId,
    connection_end: Option<ConnectionEnd>,
    client_reader: MockClientReader,
}

impl ConnectionReader for MockConnectionReader {
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<ConnectionEnd> {
        if connection_id == &self.connection_id {
            self.connection_end.clone()
        } else {
            None
        }
    }
}
```

#### Keeper

Once a message processor executes successfully, some data will typically need to be persisted in the chain state
via the private/provable store interfaces. In the same vein as for the reader defined in the previous section,
a submodule should define a trait which provides operations to persist such data.
The same considerations w.r.t. to coupling and unit-testing apply here as well.

```rust
pub trait ConnectionKeeper {
    fn store_connection(
        &mut self,
        client_id: ConnectionId,
        client_type: ConnectionType,
    ) -> Result<(), Error>;

    fn add_connection_to_client(
        &mut self,
        client_id: ClientId,
        connection_id: ConnectionId,
    ) -> Result<(), Error>;
}
```

#### Submodule implementation

We now come to the actual definition of a message processor for a submodule.

We recommend each message processor to be defined within its own Rust module, named
after the message processor itself. For example, the "Create Client" message processor of ICS 002 would
be defined in `ibc_modules::ics02_client::handler::create_client`.

##### Message type

Each message processor must define a datatype which represent the message it can process.

```rust
pub struct MsgConnectionOpenInit {
    connection_id: ConnectionId,
    client_id: ClientId,
    counterparty: Counterparty,
}
```

##### Message processor implementation

In this section we provide guidelines for implementating an actual message processor.

We divide the message processor in two parts: processing and persistance.

###### Processing

The actual logic of the message processor is expressed as a pure function, typically named
`process`, which takes as arguments a `Reader` and the corresponding message, and returns
a `HandlerOutput<T, E>`, where `T` is a concrete datatype and `E` is an error type which defines
all potential errors yielded by the message processors of the current submodule.

```rust
pub struct ConnectionMsgProcessingResult {
    connection_id: ConnectionId,
    connection_end: ConnectionEnd,
}
```

The `process` function will typically read data via the `Reader`, perform checks and validation, construct new
datatypes, emit log records and events, and eventually return some data together with objects to be persisted.

To this end, this `process` function will create and manipulate a `HandlerOutput` value like described in
the corresponding section.

```rust
pub fn process(
    reader: &dyn ConnectionReader,
    msg: MsgConnectionOpenInit,
) -> HandlerResult<ConnectionMsgProcessingResult, Error>
{
    let mut output = HandlerOutput::builder();

    let MsgConnectionOpenInit { connection_id, client_id, counterparty, } = msg;

    if reader.connection_end(&connection_id).is_some() {
        return Err(Kind::ConnectionAlreadyExists(connection_id).into());
    }

    output.log("success: no connection state found");

    if reader.client_reader.client_state(&client_id).is_none() {
        return Err(Kind::ClientForConnectionMissing(client_id).into());
    }

    output.log("success: client found");

    output.emit(ConnectionEvent::ConnectionOpenInit(connection_id.clone()));

    Ok(output.with_result(ConnectionMsgProcessingResult {
        connection_id,
        client_id,
        counterparty,
    }))
}
```

###### Persistence

If the `process` function specified above succeeds, the result value it yielded is then
passed to a function named `keep`, which is responsible for persisting the objects constructed
by the processing function. This `keep` function takes the submodule's `Keeper` and the result
type defined above, and performs side-effecting calls to the keeper's methods to persist the result.

Below is given an implementation of the `keep` function for the "Create Connection" message processors:

```rust
pub fn keep(
    keeper: &mut dyn ConnectionKeeper,
    result: ConnectionMsgProcessingResult,
) -> Result<(), Error>
{
    keeper.store_connection(result.connection_id.clone(), result.connection_end)?;
    keeper.add_connection_to_client(result.client_id, result.connection_id)?;

    Ok(())
}
```

##### Submodule dispatcher

> This section is very much a work in progress, as further investigation into what
> a production-ready implementation of the `ctx` parameter of the top-level dispatcher
> is required. As such, implementors should feel free to disregard the recommendations
> below, and are encouraged to come up with amendments to this ADR to better capture
> the actual requirements.

Each submodule is responsible for dispatching the messages it is given to the appropriate
message processing function and, if successful, pass the resulting data to the persistance
function defined in the previous section.

To this end, the submodule should define an enumeration of all messages, in order
for the top-level submodule dispatcher to forward them to the appropriate processor.
Such a definition for the ICS 003 Connection submodule is given below.

```rust
pub enum ConnectionMsg {
    ConnectionOpenInit(MsgConnectionOpenInit),
    ConnectionOpenTry(MsgConnectionOpenTry),
    ...
}
```
The actual implementation of a submodule dispatcher is quite straightforward and unlikely to vary
much in substance between submodules. We give an implementation for the ICS 003 Connection module below.

```rust
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: Msg) -> Result<HandlerOutput<()>, Error>
where
    Ctx: ConnectionReader + ConnectionKeeper,
{
    match msg {
        Msg::ConnectionOpenInit(msg) => {
            let HandlerOutput {
                result,
                log,
                events,
            } = connection_open_init::process(ctx, msg)?;

            connection::keep(ctx, result)?;

            Ok(HandlerOutput::builder()
                .with_log(log)
                .with_events(events)
                .with_result(()))
        }

        Msg::ConnectionOpenTry(msg) => // omitted
    }
}
```

In essence, a top-level dispatcher is a function of a message wrapped in the enumeration introduced above,
and a "context" which implements both the `Reader` and `Keeper` interfaces.

### Dealing with chain-specific datatypes

The ICS 002 Client submodule stands out from the other submodules as it needs
to deal with chain-specific datatypes, such as `Header`, `ClientState`, and
`ConsensusState`.

To abstract over chain-specific datatypes, we introduce a trait which specifies
both which types we need to abstract over, and their interface.

For the ICS 002 Client submodule, this trait looks as follow:

```rust
pub trait ClientDef {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;
}
```

The `ClientDef` trait specifies three datatypes, and their corresponding interface, which is provided
via a trait defined in the same submodule.

A production implementation of this interface would instantiate these types with the concrete
types used by the chain, eg. Tendermint datatypes. Each concrete datatype must be provided
with a `From` instance to lift it into its corresponding `Any...` enumeration.

For the purpose of unit-testing, a mock implementation of the `ClientDef` trait could look as follows:

```rust
struct MockHeader(u32);

impl Header for MockHeader {
  // omitted
}

impl From<MockHeader> for AnyHeader {
    fn from(mh: MockHeader) -> Self {
        Self::Mock(mh)
    }
}

struct MockClientState(u32);

impl ClientState for MockClientState {
  // omitted
}

impl From<MockClientState> for AnyClientState {
    fn from(mcs: MockClientState) -> Self {
        Self::Mock(mcs)
    }
}

struct MockConsensusState(u32);

impl ConsensusState for MockConsensusState {
  // omitted
}

impl From<MockConsensusState> for AnyConsensusState {
    fn from(mcs: MockConsensusState) -> Self {
        Self::Mock(mcs)
    }
}

struct MockClient;

impl ClientDef for MockClient {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;
}
```

Since the actual type of client can only be determined at runtime, we cannot encode
the type of client within the message itself.

Because of some limitations of the Rust type system, namely the lack of proper support
for existential types, it is currently impossible to define `Reader` and `Keeper` traits
which are agnostic to the actual type of client being used.

We could alternatively model all chain-specific datatypes as boxed trait objects (`Box<dyn Trait>`),
but this approach runs into a lot of limitations of trait objects, such as the inability to easily
require such trait objects to be Clonable, or Serializable, or to define an equality relation on them.
Some support for such functionality can be found in third-party libraries, but the overall experience
for the developer is too subpar.

We thus settle on a different strategy: lifting chain-specific data into an `enum` over all
possible chain types.

For example, to model a chain-specific `Header` type, we would define an enumeration in the following
way:

```rust
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)] // TODO: Add Eq
pub enum AnyHeader {
    Mock(mocks::MockHeader),
    Tendermint(tendermint::header::Header),
}

impl Header for AnyHeader {
    fn height(&self) -> Height {
        match self {
            Self::Mock(header) => header.height(),
            Self::Tendermint(header) => header.height(),
        }
    }

    fn client_type(&self) -> ClientType {
        match self {
            Self::Mock(header) => header.client_type(),
            Self::Tendermint(header) => header.client_type(),
        }
    }
}
```

This enumeration dispatches method calls to the underlying datatype at runtime, while
hiding the latter, and is thus akin to a proper existential type without running
into any limitations of the Rust type system (`impl Header` bounds not being allowed
everywhere, `Header` not being able to be treated as a trait objects because of `Clone`,
`PartialEq` and `Serialize`, `Deserialize` bounds, etc.)

Other chain-specific datatypes, such as `ClientState` and `ConsensusState` require their own
enumeration over all possible implementations.

On top of that, we also need to lift the specific client definitions (`ClientDef` instances),
into their own enumeration, as follows:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyClient {
    Mock(mocks::MockClient),
    Tendermint(tendermint::TendermintClient),
}

impl ClientDef for AnyClient {
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;
}
```

Messages can now be defined generically over the `ClientDef` instance:


```rust
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgCreateClient<CD: ClientDef> {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub consensus_state: CD::ConsensusState,
}

pub struct MsgUpdateClient<CD: ClientDef> {
    pub client_id: ClientId,
    pub header: CD::Header,
}
```

The `Keeper` and `Reader` traits are defined for any client:

```rust
pub trait ClientReader {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;
    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState>;
}

pub trait ClientKeeper {
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Error>;

    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: AnyClientState,
    ) -> Result<(), Error>;

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        consensus_state: AnyConsensusState,
    ) -> Result<(), Error>;
}
```

This way, only one implementation of the `ClientReader` and `ClientKeeper` trait is required,
as it can delegate eg. the serialization of the underlying datatypes to the `Serialize` bound
of the `Any...` wrappper.

Both the `process` and `keep` function are defined to take a message generic over
the actual client type:

```rust
pub fn process(
    ctx: &dyn ClientReader,
    msg: MsgCreateClient<AnyClient>,
) -> HandlerResult<CreateClientResult<AnyClient>, Error>;

pub fn keep(
    keeper: &mut dyn ClientKeeper,
    result: CreateClientResult<AnyClient>,
) -> Result<(), Error>;
```

Same for the top-level dispatcher:

```rust
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: ClientMsg<AnyClient>) -> Result<HandlerOutput<()>, Error>
where
    Ctx: ClientReader + ClientKeeper;
```

With this boilerplate out of way, one can write tests using a mock client, and associated mock datatypes
in a fairly straightforward way, taking advantage of the `From` instance to lift concerete mock datatypes
into the `Any...` enumeration:

```rust
  #[test]
  fn test_create_client_ok() {
      let client_id: ClientId = "mockclient".parse().unwrap();

      let reader = MockClientReader {
          client_id: client_id.clone(),
          client_type: None,
          client_state: None,
          consensus_state: None,
      };

      let msg = MsgCreateClient {
          client_id,
          client_type: ClientType::Tendermint,
          consensus_state: MockConsensusState(42).into(), // lift into `AnyConsensusState`
      };

      let output = process(&reader, msg.clone());

      match output {
          Ok(HandlerOutput {
              result,
              events,
              log,
          }) => {
            // snip
          }
          Err(err) => {
              panic!("unexpected error: {}", err);
          }
      }
  }
```

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
