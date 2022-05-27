# Global options

Hermes accepts global options which affect all commands.

```shell
hermes 0.15.0
Informal Systems <hello@informal.systems>
Implementation of `hermes`, an IBC Relayer developed in Rust.

FLAGS:
    -c, --config CONFIG       path to configuration file
    -j, --json                enable JSON output
```

The flags must be specified right after the `hermes` command and before any subcommand.

__Example__

To start the relayer using the configuration file at `/home/my_chain.toml` and enable JSON output:

```shell
hermes -c /home/my_chain.toml --json start
```

## JSON output

If the `--json` option is supplied, all relayer commands will output single-line JSON values instead of plain text.

Log messages will be written to `stderr`, while the final result will be written to `stdout`, and everything
will be formatted as JSON.
This allows processing only the final output using [`jq`](https://stedolan.github.io/jq/).
To process all the output using `jq`, one can redirect `stderr` to `stdout` with `hermes --json COMMAND 2>&1 | jq`.

__Example__

```shell
hermes -c /home/my_chain.toml --json create client ibc-0 ibc-1
```

```json
{"timestamp":"Apr 13 20:46:31.921","level":"INFO","fields":{"message":"Using default configuration from: '.hermes/config.toml'"},"target":"ibc_relayer_cli::commands"}
{"timestamp":"Apr 13 20:46:31.961","level":"INFO","fields":{"message":"running listener","chain.id":"ibc-1"},"target":"ibc_relayer::event::monitor"}
{"timestamp":"Apr 13 20:46:31.989","level":"INFO","fields":{"message":"running listener","chain.id":"ibc-0"},"target":"ibc_relayer::event::monitor"}
{"result":{"CreateClient":{"client_id":"07-tendermint-1","client_type":"Tendermint","consensus_height":{"revision_height":10060,"revision_number":1},"height":{"revision_height":10072,"revision_number":0}}},"status":"success"}
```

The first three lines are printed to `stderr`, while the last line with a `"result"` key is printed to `stdout`.

__Example__

To improve the readability, pipe all of the output to `jq`:

```
hermes -c /home/my_chain.toml --json create client ibc-0 ibc-1 2>&1 | jq
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

To extract the identifer of the newly created client above:

```
hermes -c /home/my_chain.toml --json create client ibc-0 ibc-1 | jq '.result.CreateClient.client_id'
```

```
"07-tendermint-2"
```
