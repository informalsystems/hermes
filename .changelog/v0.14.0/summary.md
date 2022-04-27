*April 27th, 2022*

This release notably features a new `query packet pending` command to 
list outstanding packet commitments that are either unreceived or pending 
acknowledgement at both ends of a channel.

The `ibc` crate now also come with a complete [ICS 026][ics-26] implementation.

### Note for operators

The `create channel` command now requires an existing client and connection,
unless the `--new-client-connection` flag is provided.
Please [refer to the guide][create-channel] for more information.

[ics-26]: https://github.com/cosmos/ibc/blob/master/spec/core/ics-026-routing-module/README.md
[create-channel]: http://hermes.informal.systems/commands/path-setup/channels.html#establish-channel

