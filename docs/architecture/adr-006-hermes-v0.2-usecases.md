# ADR 006: Hermes v0.2.0 Use-Cases

## Changelog
* 16.02.2021: Proposed.

## Context

One major problem with planning for the evolution of Hermes is that presently
there is insufficient clarity regarding its requirements.
It is not known who are the typical Hermes users (is it human operators or
automated pipelines?), and what are their primary use-cases.

This ADR proposes a few use-cases that seem interesting from the point
of view of a general target base of users, and which will
hopefully be a subset of the requirements of (any) future users.

Three elements that provide further context for this discussion are:

1. Hermes is still at an early stage of implementation, so these use-cases are
   not set in stone.

2. Some concrete use-cases are starting to emerge ([#628][#628]), which Hermes
   v0.1.0 either does not cover altogether, or covers poorly (e.g., because of
   inconsistent UX), thus informing this proposal.

3. Hermes is one of _three_ relayer binaries that are being developed roughly in
parallel. The other two are being developed in Go and Typescript, 
respectively (see the [references](#references) section).
In this context, it is plausible that Hermes will focus on performance,
robustness, and richness of features on a longer term.

## Decision

This is a summary of the use-cases (commands) discussed in the rest of this ADR.
Note that the commands below omit the binary name `hermes` , to keep the command
length to a minimum.

To create and update a client:
- `create client <host-chain-id> <target-chain-id>`
    - Optional params: `[--clock-drift <millis>] [--trusting-period <days>] [--trust-threshold <numerator/denominator>]`
- `update client <host-chain-id> <client-id>`

To create a connection:
- `create connection <chain-a-id> <chain-b-id>`
    - Optional: `[--delay <delay>]`
- `create connection <chain-a-id> --client-a <client-a-id> --client-b <client-b-id>`
    - Optional: `[--delay <delay>]`

To create a channel:
- `create channel <chain-a-id> <chain-b-id> --port-a <port-id> --port-b <port-id>`
    - Optional: `[--order <order>] [--version <version>]`
- `create channel <chain-a-id> --connection-a <connection-id> --port-a <port-id> --port-b <port-id>`
    - Optional: `[--order <order>] [--version <version>]`

To start packet relaying:
- `start <chain-a-id> <chain-b-id> --port-a <port-id> --port-b <port-id>`
    - Optional: `[--order <order>] [--version <version>]`
- `start <chain-a-id> --connection-a <connection-id> --port-a <port-id> --port-b <port-id>`
    - Optional: `[--order <order>] [--version <version>]`
- `start <chain-a-id> --channel-a <channel-id> --port-a <port-id>`

For finishing pre-initialized, but unfinished object handshakes, for connection and channel:
- `establish connection <chain-a-id> --connection-a <connection-id>`
- `establish channel <chain-a-id> --channel-a <channel-id> --port-a <port-id>`

### Rationale

The primary goal for the uses-cases we decided to cover is to prevent situations
where users could get stuck. For example, the output of a command may be
unclear, or there may be an error and thereby some CLI command
finishes partially, or two relayers concurrently try to perform some
operation(s) and interfere with each other, resulting in a chain state that is
obscure to the user, and then the user could consequently be stuck.

The first of the patterns below seeks to help "unblock" a user.
The second pattern is a variation on the first; this permits more efficiency
because it allows the reuse of previously-created objects in the
creation of new objects on a chain (e.g., reuse a client in the creation of a
connection, or reuse a connection in the creation of a new channel).

#### Patterns

We propose two basic patterns that Hermes should be able to fulfil.

1. Simple invocations to perform basic actions.
    - By _action_ here we mean doing the complete handshake for an object from
      scratch (specifically _connection_ or _channel_) on two chains, or
      relaying packets between two chains.
    - The focus here is for the command to include retrying mechanisms 
      (perform it _robustly_) and have the simplest interface.

2. Allow reusing of pre-existing state for basic commands.
    - The pre-existing state could be a client with some specific trust options,
      for instance, and in this case Hermes would provide support for creating
      a connection that uses this specific client.
    - This pattern should also include a retrying mechanism.

#### Details of Use-Cases

Applying the above patterns to a few cases, we get the following concrete
commands that Hermes v0.2.0 should fulfil.

##### Create & Update a Client

- Minimal invocation: this will create the client from scratch:

```
create client <host-chain-id> <target-chain-id> [--clock-drift <millis>] [--trusting-period <days>] [--trust-threshold <numerator/denominator>]
```

**Details:**
Submits a transaction of type [client create][client-create] to chain
`<host-chain-id>` (sometimes called the _destination_ chain of this
transaction). The new client will be verifying headers for
chain `<target-chain-id>` (often called the _source_ chain).

See also the [limitations](#limitations) section discussing the optional
security parameters for this command.

- Update a client:

```
update client <host-chain-id> <client-id>
```

**Details:**
Submits a transaction to chain id `<host-chain-id>` to update the client having
identifier `<client-id>` with new consensus state from up-to-date headers.
Hermes will automatically infer the target chain of this client from
the [client state][client-state].

- Upgrade a client:

```
upgrade client <host-chain-id> <client-id>
```

**Details:**
Submits a transaction to chain id `<host-chain-id>` to upgrade the client having
identifier `<client-id>`. 
Hermes will automatically infer the target chain of this client from
the [client state][client-state].

- Upgrade all clients that target a specific chain:

```
upgrade clients <target-chain-id> 
```

**Details:**
Submits a transaction to upgrade clients of all chains in the config that target
chain id `<target-chain-id>`.

##### Create New Connection

- Minimal invocation: this will create the connection from scratch, using
  _new_ clients:

```
create connection <chain-a-id> <chain-b-id> [--delay <delay>]
```

**Details:**
Starts a transaction to perform the connection open handshake protocol between
two chains.
The chains are called symbolically `a` and `b`, hence the option names
`<chain-a-id>` and `<chain-b-id>`. In all handshakes, Hermes submits the first
step (typically called _init_, e.g., `ConnOpenInit`), to side `a`, then the
second step (e.g., `ConnOpenTry`) to side `b`, and so on.

The optional parameter `--delay` is the delay period that the new connection
should have. Note also the [limitations](#limitations) around the
`delay_period` feature.

- Reusing pre-existing state, concretely, with _existing_ clients:

```
create connection <chain-a-id> --client-a <client-id> --client-b <client-id> [--delay <delay>]
```

**Details:**
Similar to the previous command, this command will perform the connection
open handshake protocol, but will reuse the client with identifier from
option `--client-a`. This client is expected to exist on chain `<chain-a-id>`.
The target chain of this client is identified in the
[client state][client-state] (concretely, the target chain is represented under
`chain_id` field of the client state), which provides the identifier for the 
side `b` of the new connection. On the side `b` chain, this command will
establish the connection using the client with identifier from the option
`--client-b`, which must be verifying headers for chain `<chain-a-id>`.

##### Create New Channel

- With _new_ connection and clients:

```
create channel <chain-a-id> <chain-b-id> --port-a <port-id> --port-b <port-id> [--order <order>] [--version <version>]
```

- With _existing_ specific connection:

```
create channel <chain-a-id> --connection-a <connection-id> --port-a <port-id> --port-b <port-id> [--order <order>] [--version <version>]
```

##### Packet Relaying

- relay packets over a _new_ channel, _new_ connection, and _new_ clients:

```
start <chain-a-id> <chain-b-id> --port-a <port-id> --port-b <port-id> [--order <order>] [--version <version>]
```

- relay packets over a _new_ channel that re-uses an _existing_ connection:

```
start <chain-a-id> --connection-a <connection-id> --port-a <port-id> --port-b <port-id> [--order <order>] [--version <version>]
```

- relay packets over an _existing_ channel:

```
start <chain-a-id> --channel-a <channel-id> --port-a <port-id>
```

##### Finishing partially complete handshakes:

These commands serve the purpose of covering certain corner-cases where a
handshake may be partially started.

- Finalize handshake for _partially established_ connection:

```
establish connection <chain-a-id> --connection-a <connection-id>
```

- Finalize handshake for _partially established_ channel:

```
establish channel <chain-a-id> --channel-a <channel-id> --port-a <port-id>
```


### Command Output

By default, the command will provide human-readable output, i.e., pretty
printing.
In practice, the final result of a Hermes command is captured in an 
[Output][output] structure that has support for JSON serialization. To
enable JSON, we add a configuration parameter `log_json`. The global section
of the config file will look as follows:

```toml
[global]
log_level = 'error'
log_json = 'false'
```

By default, this parameter is `false`. When set to `true`, all the Hermes output
will be in JSON.

## Status

Partially implemented.

## Consequences
### Positive

- Simpler, more accurate CLI invocation: "create" is more precise than "tx" or
  "handshake"
- Improved output for human operators.

### Negative

- Some commands will possibly turn out to be useless.
- Requires some rethinking of the Relayer architecture (mainly because of the
  [limitations](#limitations) surrounding light clients.)

### Neutral


## References

- Relayer in Go: https://github.com/cosmos/relayer
- Relayer in Typescript: https://github.com/confio/ts-relayer



[#628]: https://github.com/informalsystems/hermes/issues/628
[#673]: https://github.com/informalsystems/hermes/issues/673
[#640]: https://github.com/informalsystems/hermes/issues/640
[client-state]: https://hermes.informal.systems/documentation/commands/queries/client.html#query-the-client-state
[client-create]: https://docs.rs/ibc/0.1.1/ibc/ics02_client/msgs/create_client/index.html
[output]: https://github.com/informalsystems/hermes/blob/1f2e72dbcafee5a8bbdab381ff4927d5870b4b59/relayer-cli/src/conclude.rs#L80
