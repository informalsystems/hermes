- Allow relaying ICS-04 packets with non-UTF-8 payloads ([\#3770](https://github.com/informalsystems/hermes/issues/3770))
  Hermes does not assume anymore that an ICS-04 packet data is valid UTF-8,
  by using the `packet_data_hex` attribute when assembling a packet from events, instead of the deprecated `packet_data` attribute.
  Relying on the `packet_data` attribute enforces a UTF-8 encoded payload (eg. JSON), disallowing eg. Protobuf-encoded payloads.
  The `packet_data` attribute [has been deprecated][0] in favor of `packet_data_hex` since IBC-Go v1.0.0.
  [0]: https://github.com/cosmos/ibc-go/blob/fadf8f2b0ab184798d021d220d877e00c7634e26/CHANGELOG.md?plain=1#L1417
