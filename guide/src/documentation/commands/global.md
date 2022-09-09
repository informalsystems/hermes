# Global options

Hermes accepts _global_ options which affect all commands.

```shell
hermes {{#template ../../templates/version.md}}
Informal Systems <hello@informal.systems>
Implementation of `hermes`, an IBC Relayer developed in Rust.

FLAGS:
        --config <CONFIG>    Path to configuration file
        --json               Enable JSON output
```

## Ordering of command-line options

The global options must be specified right after the `hermes` command and _before_ any sub-command.
The non-global options have to be specified _after_ the sub-command.

```shell
hermes [GLOBAL_OPTIONS] <SUBCOMMAND> [OPTIONS]
```

__Example__

To `start` Hermes using the configuration file at `/home/my_chain.toml` and enable JSON output:

```shell
{{#template ../../templates/commands/hermes/start_1.md GLOBALOPTIONS=--config $HOME/my_chain.toml --json}}
```

To `query` all clients on a chain while enabling JSON output:

```shell
{{#template ../../templates/commands/hermes/query/clients_1.md HOST_CHAIN_ID=ibc-1 GLOBALOPTIONS=--json}}
```

## JSON output

If the `--json` option is supplied, all commands will output single-line JSON values instead of plain text.

Log messages will be written to `stderr`, while the final result will be written to `stdout`, and everything
will be formatted as JSON.
This allows processing only the final output using [`jq`](https://stedolan.github.io/jq/).
To process all the output using `jq`, one can redirect `stderr` to `stdout` with `hermes --json COMMAND 2>&1 | jq`.

__Example__

```shell
{{#template ../../templates/commands/hermes/create/client_1.md HOST_CHAIN_ID=ibc-0 REFERENCE_CHAIN_ID=ibc-1 GLOBALOPTIONS=--json}}
```

```json
{"timestamp":"Apr 13 20:46:31.921","level":"INFO","fields":{"message":"Using default configuration from: '.hermes/config.toml'"},"target":"ibc_relayer_cli::commands"}
{"timestamp":"Apr 13 20:46:31.961","level":"INFO","fields":{"message":"running listener","chain.id":"ibc-1"},"target":"ibc_relayer::event::monitor"}
{"timestamp":"Apr 13 20:46:31.989","level":"INFO","fields":{"message":"running listener","chain.id":"ibc-0"},"target":"ibc_relayer::event::monitor"}
{"result":{"CreateClient":{"client_id":"07-tendermint-1","client_type":"Tendermint","consensus_height":{"revision_height":10060,"revision_number":1},"height":{"revision_height":10072,"revision_number":0}}},"status":"success"}
```

The first three lines are printed to `stderr`, while the last line with a `"result"` key is printed to `stdout`.

__Example__

To improve the readability, pipe all the output to `jq`:

```
{{#template ../../templates/commands/hermes/create/client_1.md HOST_CHAIN_ID=ibc-0 REFERENCE_CHAIN_ID=ibc-1 GLOBALOPTIONS=--json}} 2>&1 | jq
```

```json
{
  "timestamp": "Apr 13 20:52:26.060",
  "level": "INFO",
  "fields": {
    "message": "Using default configuration from: '.hermes/config.toml'"
  },
  "target": "ibc_relayer_cli::commands"
}
{
  "timestamp": "Apr 13 20:52:26.082",
  "level": "INFO",
  "fields": {
    "message": "running listener",
    "chain.id": "ibc-1"
  },
  "target": "ibc_relayer::event::monitor"
}
{
  "timestamp": "Apr 13 20:52:26.088",
  "level": "INFO",
  "fields": {
    "message": "running listener",
    "chain.id": "ibc-0"
  },
  "target": "ibc_relayer::event::monitor"
}
{
  "result": {
    "CreateClient": {
      "client_id": "07-tendermint-5",
      "client_type": "Tendermint",
      "consensus_height": {
        "revision_height": 10364,
        "revision_number": 1
      },
      "height": {
        "revision_height": 10375,
        "revision_number": 0
      }
    }
  },
  "status": "success"
}
```

__Example__

To extract the identifier of the newly created client above:

```
{{#template ../../templates/commands/hermes/create/client_1.md HOST_CHAIN_ID=ibc-0 REFERENCE_CHAIN_ID=ibc-1 GLOBALOPTIONS=--json}} | jq '.result.CreateClient.client_id'
```

Which should output:

```
"07-tendermint-2"
```
