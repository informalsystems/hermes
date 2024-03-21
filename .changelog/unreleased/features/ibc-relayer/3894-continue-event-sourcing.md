- Improve reliabily of event source in `pull` mode by proceeding to next block even if Hermes cannot parse the current block.
  Add new configuration option to `event_source` setting: `max_retries` defines how many times Hermes should attempt to pull a block over RPC.
  ```toml
  event_source = { mode = 'pull', interval = '1s', max_retries = 4 }
  ```
  ([\#3894](https://github.com/informalsystems/hermes/issues/3894))
