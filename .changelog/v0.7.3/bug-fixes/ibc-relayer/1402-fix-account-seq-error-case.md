- Only increase cached account sequence number when `broadcast_tx_sync` fails,
  therefore ensuring that the cached sequence number stays in sync with the
  node. ([#1402](https://github.com/informalsystems/ibc-rs/issues/1402))