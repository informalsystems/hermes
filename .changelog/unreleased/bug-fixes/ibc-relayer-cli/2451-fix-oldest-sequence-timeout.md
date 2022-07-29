
- renamed `oldest_sequence` as `backlog_oldest_sequence`
- Renamed `oldest_timestamp` as `backlog_oldest_timestamp`
- introduced backlog_size to complement the other backlog_* data, as a metric reporting how many packets are pending on a channel
- Ensures the `backlog_oldest_sequence` and `backlog_oldest_timestamp` are correctly updated when a timeout occurs or when another relayer clears the channel.
  ([#2451](https://github.com/informalsystems/ibc-rs/issues/2451))
- Ensures `backlog_timestamp` is never updated by a packet with a higher `sequence` than the oldest pending packet.([#2469](https://github.com/informalsystems/ibc-rs/issues/2469))
