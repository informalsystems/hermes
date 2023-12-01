*November 28th, 2023*

This patch release of Hermes adds a metric to improve monitoring errors and one
to measure the efficiency of the client update skip feature released in patch v1.7.1.

* `broadcast_errors` records the number of times a specific error is observed by Hermes when broadcasting transactions.
* `client_updates_skipped` records the number of client updates skipped due to the consensus states already existing.
