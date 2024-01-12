- Improve resilience when relaying on ordered channels. When a packet
  fails to be relayed on an ordered channel, this used to block the
  channel until either another relayer relayed the packet successfully or
  until packet clearing kicked off. Hermes will now detect the failure
  and attempt to clear packets on the channel in order to unblock it.
  ([\#3540](https://github.com/informalsystems/hermes/issues/3540))
