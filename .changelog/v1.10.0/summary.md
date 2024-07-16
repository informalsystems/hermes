*June 24th, 2024*

This release enhances filter configurations and includes the following updates:

1. `excluded_sequences` supports sequence ranges in addition to exact values,
   e.g. `[1, 2, "5-10", 13]` is now valid.
2. `packet_filter` now ignores unintended whitespace.
3. A new `allow_ccq` per-chain configuration has been added to skip the relaying of
   ICS31 Cross Chain Queries.

Additionally, various improvements to testing and bug fixes have been implemented.
