# Configure Hermes

In order to run Hermes, you will need to have a configuration file.

The format supported for the configuration file is [TOML](https://toml.io/en/).

By default, Hermes expects the configuration file to be located at `$HOME/.hermes/config.toml`.

This can be overridden by supplying the `--config` flag when invoking `hermes`, before the
name of the command to run, e.g. `hermes --config my_config.toml query connection channels --chain ibc-1 --connection connection-1`.

> The current version of Hermes does not support managing the configuration file programmatically.
> You will need to use a text editor to create the file and add content to it.

```bash
hermes [--config CONFIG_FILE] COMMAND
```

## Table of contents

<!-- toc -->

## Configuration

The configuration file must have one `global` section, and one `chains` section for each chain.
<!-- markdown-link-check-disable -->
> **Note:** As of 0.6.0, the Hermes configuration file is self-documented.
> Please read the configuration file [`config.toml`](https://github.com/informalsystems/hermes/blob/{{#include ../../templates/version.md}}/config.toml)
> itself for the most up-to-date documentation of parameters.


By default, Hermes will relay on all channels available between all the configured chains.
In this way, every configured chain will act as a source (in the sense that Hermes listens for events)
and as a destination (to relay packets that others chains have sent).

For example, if there are only two chains configured, then Hermes will only relay packets between those two,
i.e. the two chains will serve as a source for each other, and likewise as a destination for each other's relevant events.
Hermes will ignore all events that pertain to chains which are unknown (i.e. not present in config.toml).

To restrict relaying on specific channels, or uni-directionally, you can use [packet filtering policies](https://github.com/informalsystems/hermes/blob/{{#include ../../templates/version.md}}/config.toml#L209-L231).
<!-- markdown-link-check-enabled -->

## Adding private keys

For each chain configured you need to add a private key for that chain in order to submit [transactions](../commands/tx/index.md),
please refer to the [Keys](../commands/keys/index.md) sections in order to learn how to add the private keys that are used by Hermes.

## Connecting via TLS

Hermes supports connection via TLS for use-cases such as connecting from behind
a proxy or a load balancer. In order to enable this, you'll want to set the
`rpc_addr`, `grpc_addr`, or `websocket_addr` parameters to specify a TLS
connection via HTTPS using the following scheme (note that the port number 443
is just used for example):
```
rpc_addr = 'https://domain.com:443'
grpc_addr = 'https://domain.com:443'
websocket_addr = 'wss://domain.com:443/websocket'
```

## Support for Interchain Accounts

As of version 0.13.0, Hermes supports relaying on [Interchain Accounts][ica] channels.

If the `packet_filter` option in the chain configuration is disabled, then
Hermes will relay on all existing and future channels, including ICA channels.

There are two kinds of ICA channels:

1. The host channels, whose port is `icahost`
2. The controller channels, whose port starts with `icacontroller-` followed
   by the owner account address. [See the spec for more details][ica].

If you wish to only relay on a few specific standard channels (here `channel-0` and `channel-1`),
but also relay on all ICA channels, you can specify the following packet filter:

> Note the use of wildcards in the port and channel identifiers (`['ica*', '*']`)
> to match over all the possible ICA ports.

```toml
[chains.packet_filter]
policy = 'allow'
list = [
  ['ica*', '*'], # allow relaying on all channels whose port starts with `ica`
  ['transfer', 'channel-0'],
  ['transfer', 'channel-1'],
  # Add any other port/channel pairs you wish to relay on
]
```

If you wish to relay on all channels but not on ICA channels, you can use
the following packet filter configuration:

```toml
[chains.packet_filter]
policy = 'deny'
list = [
  ['ica*', '*'], # deny relaying on all channels whose port starts with `ica`
]
```

## Connecting to a full node protected by HTTP Basic Authentication

To connect to a full node protected by [HTTP Basic Authentication][http-basic-auth],
specify the username and password in the `rpc_addr`, `grpc_addr` and `websocket_addr` settings
under the chain configuration in `config.toml`.

Here is an example with username `hello` and password `world`, assuming the RPC, WebSocket and gRPC servers
listen on domain `mydomain.com` with TLS enabled (HTTPS/WSS).

```toml
[[chains]]
id = 'my-chain-0'

# ...

rpc_addr = 'https://hello:world@mydomain.com:26657'
grpc_addr = 'https://hello:world@mydomain.com:9090'
websocket_addr = 'wss://hello:world@mydomain.com:26657/websocket'

# ...
```

> **Caution:** Warning: The "Basic" authentication scheme sends the credentials encoded but not encrypted.
> This would be completely insecure unless the exchange was over a secure connection (HTTPS/TLS).

[http-basic-auth]: https://developer.mozilla.org/en-US/docs/Web/HTTP/Authentication
[ica]: https://github.com/cosmos/ibc/blob/master/spec/app/ics-027-interchain-accounts/README.md
