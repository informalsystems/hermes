- Improve resilience when relaying on ordered channels. 
  When relaying packets on an ordered channel, Hermes will now attempt
  to detect whether the next message to send has the sequence number
  expected on that channel. If there is a mismatch, then Hermes will trigger a packet
  clear on the channel to unblock it before resuming operations on that channel.
  ([\#3540](https://github.com/informalsystems/hermes/issues/3540))
