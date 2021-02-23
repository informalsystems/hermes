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

2. Some concrete use-cases are starting to emerge ([#628][628]), which Hermes
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
- `create client ibc-0 ibc-1`
    - Optional params: `[--clock-drift <millis>] [--trusting-period <days>] [--trust-threshold <numerator/denominator>]`
- `update client ibc-0 <client-id>`

To create a connection:
- `create connection ibc-0 ibc-1`
    - Optional: `[--delay <delay>]`
- `create connection ibc-0 --src-client <client-id> --dst-client <client-id>`
    - Optional: `[--delay <delay>]`

To create a channel:
- `create channel ibc-0 ibc-1 --src-port <port-id> --dst-port <port-id>`
    - Optional: `[--order <order>] [--version <version>] [--delay <delay>]`
- `create channel ibc-0 --src-connection <connection-id> --src-port <port-id> --dst-port <port-id>`
    - Optional: `[--order <order>] [--version <version>]`

To start packet relaying:
- `start ibc-0 ibc-1 --src-port <port-id> --dst-port <port-id>`
    - Optional: `[--order <order>] [--version <version>] [--delay <delay>]`
- `start ibc-0 --src-connection <connection-id> --src-port <port-id> --dst-port <port-id>`
    - Optional: `[--order <order>] [--version <version>]`
- `start ibc-0 --src-channel <channel-id>`

For finishing pre-initialized, but unfinished object handshakes, for connection and channel:
- `establish connection ibc-0 --src-connection <connection-id>`
- `establish channel ibc-0 --src-port <port-id> --src-channel <channel-id>`

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
create client ibc-0 ibc-1 [--clock-drift <millis>] [--trusting-period <days>] [--trust-threshold <numerator/denominator>]
```

**Details:**
Submits a transaction of type "client create" to chain `ibc-0` (called the
_destination_ chain). The new client will be verifying headers for chain
`ibc-1` (called a _source_ chain).

See also the [limitations](#limitations) section discussing the optional
security parameters for this command.

- Update a client:

```
update client ibc-0 <client-id>
```
**Details:**
Submits a transaction to chain `ibc-0` to update the client having identifier
`<client-id>` with new consensus state. Hermes will automatically infer
the source chain of this client from the [client state][client-state].

##### Create New Connection

- Minimal invocation: this will create the connection from scratch, using
  _new_ clients:

```
create connection ibc-0 ibc-1 [--delay <delay>]
```

**Details:**
Starts a transaction to perform the connection open handshake protocol between
chains `ibc-0` and `ibc-1`. The optional parameter `--delay` is the delay period
that the new connection should have.

- Reusing pre-existing state, concretely, with _existing_ clients:

```
create connection ibc-0 --src-client <client-id> --dst-client <client-id> [--delay <delay>]
```

**Details:**
Similar to the previous command, but will reuse the client with identifier from
option `--src-client` which is expected to exist on chain `ibc-0`. The
[client state][client-state] from this client will also provide the identifier 
for the destination chain (this is the "chain_id" field from the client state).
Similarly, on the destination chain, this command will establish the connection
using the client with identifier from the option `--dst-client`, which must
be verifying headers for the source chain.

##### Create New Channel

- With _new_ connection and clients:

```
create channel ibc-0 ibc-1 --src-port <port-id> --dst-port <port-id> [--order <order>] [--version <version>] [--delay <delay>]
```

- With _existing_ specific connection:

```
create channel ibc-0 --src-connection <connection-id> --src-port <port-id> --dst-port <port-id> [--order <order>] [--version <version>]
```

##### Packet Relaying

- relay packets over a _new_ channel, _new_ connection, and _new_ clients:

```
start ibc-0 ibc-1 --src-port <port-id> --dst-port <port-id> [--order <order>] [--version <version>] [--delay <delay>]
```

- relay packets over a _new_ channel that re-uses an _existing_ connection:

```
start ibc-0 --src-connection <connection-id> --src-port <port-id> --dst-port <port-id> [--order <order>] [--version <version>]
```

- relay packets over an _existing_ channel:

```
start ibc-0 --src-channel <channel-id>
```

##### Finishing partially complete handshakes:

These commands serve the purpose of covering certain corner-cases where a
handshake may be partially started.

- Finalize handshake for _partially established_ connection:

```
establish connection ibc-0 --src-connection <connection-id>
```

- Finalize handshake for _partially established_ channel:

```
establish channel ibc-0 --src-channel <channel-id>
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
timeout = '10s'
strategy = 'naive'
log_level = 'error'
log_json = 'false'
```

By default, this parameter is `false`. When set to `true`, all the Hermes output
will be in JSON.

## Status

Partially implemented.

## Limitations

There are currently certain limitations on how a light client can be
instantiated, which can pose issues to the "client create" use-case that has
parametrized trust options.
(The discussion in [673] provides further context on this.)
Consequently, the parametrized client create use-case may involve more complex
discussions and may not be handled within v0.2.0.

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



[628]: https://github.com/informalsystems/ibc-rs/issues/628
[673]: https://github.com/informalsystems/ibc-rs/issues/673
[client-state]: https://hermes.informal.systems/query_client.html#query-the-client-state
[output]: https://github.com/informalsystems/ibc-rs/blob/1f2e72dbcafee5a8bbdab381ff4927d5870b4b59/relayer-cli/src/conclude.rs#L80