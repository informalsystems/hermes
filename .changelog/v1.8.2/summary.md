*March 12th, 2024*

This release fixes the two following bugs and improves the connection and channel handshake retry mechanism:

* Fix erroneous warnings for incompatible version of IBC-Go during health checks, ensuring accurate compatibility reporting
* Fix a bug in the `clear packets` command which caused packet clearing to fail with an "counterparty channel not found" error
