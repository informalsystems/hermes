- Add a `--packet-sequences` flag to the `clear packets`, `tx packet-recv`, and `tx packet-ack` commands.
  When this flag is specified, these commands will only clear the packets with the specified sequence numbers
  on the given chain. If not provided, all pending packets will be cleared on both chains, as before.

  This flag takes either a single sequence number or a range of sequences numbers.
  Each element of the comma-separated list must be either a single sequence number or 
  a range of sequence numbers.

  Examples:
  - `10` will clear a single packet with sequence nymber `10`
  - `1,2,3` will clear packets with sequence numbers `1, 2, 3`
  - `1..5` will clear packets with sequence numbers `1, 2, 3, 4, 5`
  - `..5` will clear packets with sequence numbers `1, 2, 3, 4, 5`
  - `5..` will clear packets with sequence numbers greater than or equal to `5`
  - `..5,10..20,25,30..` will clear packets with sequence numbers `1, 2, 3, 4, 5, 10, 11, ..., 20, 25, 30, 31, ...`
  - `..5,10..20,25,30..` will clear packets with sequence numbers `1, 2, 3, 4, 5, 10, 11, ..., 20, 25, 30, 31, ...`

  ([\#3672](https://github.com/informalsystems/hermes/issues/3672))
