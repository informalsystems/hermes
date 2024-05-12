*March 6th, 2024*

This release improves reliability when relaying, more enhanced configuration and improved monitoring.

Reliability has been improved:
* It is now possible to relay ICS-04 packets with non-UTF-8 payloads
* Packet sequences are now verified for ordered channels before trying to relay

Additional per-chain configurations have been added:
* `excluded_sequences` used to skip problematic packets when clearing
* `memo_overwrite` allowing users to overwrite the relayer memo when chains have a
strict limit for the size of the memo

Monitoring issues improvements:
* A new metric `simulate_errors` which counts the number of failed simulated transactions
* Out of gas error diagnostic gives more information and a dedicated entry to the guide has been added
* Failed gas simulation will not be considered as unrecoverable for legacy chains
* The compatibility check during the health-check has been improved will assess more correctly the versions
  for Ibc-Go and Cosmos SDK
