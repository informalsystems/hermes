*March 12th, 2024*

This release, v1.8.2, focuses on bug fixes and improvements in connection
and channel handshake mechanisms.

The connection and channel handshake retry strategy has been improved.

Two bugs have been fixes:
* One where erroneous warnings for incompatible versions were generated during health checks, ensuring accurate compatibility reporting.
* Another which caused the `packet clear` command to fail with an unfound channel ID error.
