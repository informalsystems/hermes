WIP

# Setup
## Prerequisites (OSx)
See Thane's notes [here](https://hedgedoc.informal.systems/G3PkdLXKT86oOTGWrGQe5g#).

### PSQL
No need to setup the tendermint stuff.

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
- start the `dev-env` script (doesn't work with three chains):
  ```
  ./scripts/dev-env ~/.hermes/config.toml ibc-0 ibc-1
  ```
  Tested with gaia v7.0.0

## Run hermes CLIs
- create IBC client
  ```
  $ hermes create client ibc-0 ibc-1
  2022-05-04T19:58:37.942880Z  INFO ThreadId(01) using default configuration from '/Users/ancaz/.hermes/config.toml'
  2022-05-04T19:58:37.973893Z  INFO ThreadId(35) send_tx_commit{id=create client}: wait_for_block_commits: waiting for commit of tx hashes(s) AD23A756AA297E18CBED3AF24270CCD933F04C2A17DE7410D5C38AE1572F3E7B id=ibc-0
  Error: foreign client error: error raised while creating client for chain ibc-0: failed sending message to dst chain : failed tx: no confirmation
  ```
  All CLIs will fail to retrieve the Tx hash as the queries are not yet changed to do psql queries. 

## Check psql
- check that the transaction appears in the `tx_results` table (there should be b:
  ```
  $ psql -U tendermint -c "select tx_hash from tx_results  where tx_hash = 'AD23A756AA297E18CBED3AF24270CCD933F04C2A17DE7410D5C38AE1572F3E7B'" ibc0
  tx_hash
  ------------------------------------------------------------------
  AD23A756AA297E18CBED3AF24270CCD933F04C2A17DE7410D5C38AE1572F3E7B
  (1 row)
  ```

