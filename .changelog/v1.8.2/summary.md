*March 12th, 2024*

This release, v1.8.2, focuses on bug fixes and improvements in connection
and channel handshake mechanisms.

The connection and channel handshake retry strategy has been improved.

Two bugs have been fixes:
* One which was generating warning for incompatible versions during the health-check.
* Another which caused the `packet clear` command to fail with an unfound channel ID error.
