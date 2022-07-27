WIP

# Setup
## Prerequisites (OSx)
See Thane's notes [here](https://hedgedoc.informal.systems/G3PkdLXKT86oOTGWrGQe5g#).

### PSQL
Tested with following changes:
- edit `~/.pgpass` to read something like:
    ```
    # hostname:port:database:username:password
    localhost:5432:postgres:postgres:ibcnode
    localhost:5432:ibc0:tendermint:tendermint:tendermint
    localhost:5432:ibc1:tendermint:tendermint:tendermint
    ```
- add trust for local here:
    ```
    sudo vim /Library/PostgreSQL/14/data/pg_hba.conf
    ```
- restart:
    ```
    sudo -u postgres pg_ctl reload -D /Library/PostgreSQL/14/data/
    ```
## Start the chains (gaia v7.0.0)
- start the `dev-env` script (doesn't work yet with three chains):
  ```
  ./scripts/dev-env ~/.hermes/config.toml ibc-0 ibc-1
  ```
  Tested with gaia v7.0.0

The script does the following:
- sets up psql
  - removes the old database and role
  - creates the tendermint DB
  - loads the [schema](https://github.com/informalsystems/ibc-rs/blob/anca/ibcnode/relayer-x/schema.sql)
- configures psql indexer in tendermint config files
- starts two gaia chains

## Run hermes

### Run hermes and the IBC proxy node
In this mode hermes is configured to send all the RPC requests to the IBC proxy node who performs psql queries for all Tx RPC queries and relays all others RPCs to `<ibc_proxy_rpc_port>`.

See here how to [start the IBC proxy node](https://github.com/informalsystems/ibc-rs/blob/anca/ibcnode/relayer-x/ibc-proxy/README.md)
Hermes chain configuration should look like this (type shown for clarification, `CosmosSdk` is the default and can be omitted):
  ```
  [[chains]]
  id = 'ibc-0'
  type = 'CosmosSdk'
  rpc_addr = 'http://127.0.0.1:<ibc_proxy_rpc_port>'
  grpc_addr = 'http://127.0.0.1:9090'
  websocket_addr = 'ws://127.0.0.1:26657/websocket'
  ```

### Run hermes with `CosmosPsql` configured chains
In this mode hermes performs psql queries on the Tendermint and IBC psql DBs.
Hermes chain configuration should look like this:
  ```
  [[chains]]
  id = 'ibc-0'
  type = 'CosmosPsql'
  psql_conn = 'postgres://tendermint:tendermint@localhost/ibc0'
  rpc_addr = 'http://127.0.0.1:26657'
  grpc_addr = 'http://127.0.0.1:9090'
  websocket_addr = 'ws://127.0.0.1:26657/websocket'
  ```

### pSQL and Queries
A few tables are maintained by a psql enabled tendermint node. See the [schema.sql](https://github.com/informalsystems/ibc-rs/blob/anca/ibcnode/relayer-x/schema.sql) file for a description.
In addition, on start, the relayer creates the `ibc_json` table if not already created.
It stores snapshots of the chain IBC data (in json format) for the last N heights (N=8, hardcoded atm).

### Tendermint queries
All tendermint RPCs that use the indexer have been implemented:
- Tx by hash - required for all hermes CLIs and packet relaying
- client header by id and height - required to retrieve headers used in previous client updates (misbehavior)
- packet data by packet fields
- block query - required to extract events from begin/end block

Other tendermint RPCs stay the same (e.g. query with proofs)

### Application queries
Currently the IBC snapshot per height includes:
- the chain status, used for `query_application_status()`
- connection information, used to query connection(s)
- channel information, used to query channel(s)
- send packets, used to query packet data (instead of `query_txs()`)

The IBC DB is currently maintained and used only by `hermes start`.
All other CLIs still use gRPC to query the application state and sqlx for some of the tendermint queries (`query_txs()` and `query_blocks()`)
