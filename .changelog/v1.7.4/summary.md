*December 15th, 2023*

This release improves the monitoring of Hermes instances by fixing the `broadcast_errors` metric so
that it correctly batches the same errors together. It also improves the metrics `backlog_*` by
updating them whenever Hermes queries pending packets.

This release also improves the reliability of the idle worker clean-up and 
fixes a bug within the `evidence` command which would sometimes prevent
the misbehaviour evidence from being reported.
