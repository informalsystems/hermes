Multiple fixes related to telemetry, detailed below ([#2479]).

- Renamed the following metrics:
  * `ibc_client_updates` to `client_updates_submitted`
  * `ibc_client_misbehaviours ` to `client_misbehaviours_submitted`
  * `ibc_receive_packets` to `receive_packets_confirmed`
  * `ibc_acknowledgment_packets ` to `acknowledgment_packets_confirmed`
  * `ibc_timeout_packets ` to `timeout_packets_confirmed`
  * `cache_hits` to `queries_cache_hits`
  * `msg_num` to `total_messages_submitted`
  * `send_packet_count` to `send_packet_events`
  * `acknowledgement_count` to `acknowledgement_events`
  * `cleared_send_packet_count` to `cleared_send_packet_events`
  * `cleared_acknowledgment_count` to `cleared_acknowledgment_events`

- Added the following metric:
  * `timeout_events`

- Fixed the following metrics:
  * `client_updates_submitted`: Now correctly count all ClientUpdate messages
  * `total_messages_submitted`: Now count only submitted messages

- Changed telemetry `enabled` to `false` in the vanilla config.toml, to match the default value for this parameter.
- Changed `misbehaviour` to `false` in the vanilla config.toml, to match the default value for this parameter.

  ([#2479](https://github.com/informalsystems/ibc-rs/issues/2479))