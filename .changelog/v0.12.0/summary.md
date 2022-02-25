This release notably brings compatibility with Cosmos SDK 0.45 and IBC v3.0.0,
as well as support for non-standard ports in the channel handshake.
It also contains a fix for a bug where `SendPacket` events were duplicated when emitted at EndBlock,
and fixes another bug where Hermes would clear packet at startup even when `clear_on_start = false`.
Additionally, a new CLI command `clear packets` has been added for clearing packets in both direction on a given channel.
The relayer will now also honor the `tracing` filter specified in the `RUST_LOG` environment variable, if any.

### Note for operators

As of this release, the relayer will not respond to the `SIGHUP` signal and will therefore
not reload the configuration anymore. This feature has been deemed unnecessary given the
recent performance improvements, and it is now recommended to just restart the relayer
when the configuration is updated.
