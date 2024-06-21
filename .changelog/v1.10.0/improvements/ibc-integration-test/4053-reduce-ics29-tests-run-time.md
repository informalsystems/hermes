- Reduce run time for ICS29 tests by immediately verifying if either
  the legacy fees, `recv_fee + ack_fee + timeout_fee` or current
  fees, `max(recv_fee + ack_fee, timeout_fee)` have been escrowed.
  ([\#4053](https://github.com/informalsystems/hermes/issues/4053))