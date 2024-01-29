- Add a `query_packets_chunk_size` config option and a `--query-
  packets-chunk-size flag to the `clear packets` CLI to configure how
  many packets to query at once from the chain when clearing pending
  packets. Lower this setting if one or more of packets you are
  trying to clear are huge and make the packet query time out or fail.
  ([\#3743](https://github.com/informalsystems/hermes/issues/3743))
