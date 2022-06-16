- Fix `recv_packet` handler incorrectly querying `packet_receipt` and `next_sequence_recv` using
  packet's `source_{port, channel}`.
  ([#2293](https://github.com/informalsystems/ibc-rs/issues/2293))
