This release notably features a new [`query packet pending`][pending] command to
list outstanding packet commitments that are either unreceived or pending
acknowledgement at both ends of a channel.

The `ibc` crate now also come with a complete [ICS 026][ics-26] implementation.

### Note for operators

There is a new `query packet pending` command, see above for more information.

The `create channel` command now requires an existing client and connection,
unless the `--new-client-connection` flag is provided.
Please [refer to the guide][create-channel] for more information.

[ics-26]: https://github.com/cosmos/ibc/blob/master/spec/core/ics-026-routing-module/README.md
[pending]: https://hermes.informal.systems/documentation/commands/queries/packet.html#pending-packets
[create-channel]: https://hermes.informal.systems/documentation/commands/path-setup/channels.html#establish-channel
