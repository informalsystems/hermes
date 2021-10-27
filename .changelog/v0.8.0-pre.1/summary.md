This is a pre-release which depends on forks of various Rust libraries.
As such, it is advised to avoid depending on the `ibc` and `ibc-relayer` crates
at version 0.8.0-pre.1.

However, Hermes v0.8.0-pre.1 is considered stable and it is recommended for all
users to update to this version.

This release notably includes a new [`memo_prefix`][memo] configuration option
for specifying a prefix to be include in the memo of each transaction submitted
by Hermes.
