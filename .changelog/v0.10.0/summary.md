*January 13th, 2021*

This release notably updates the underlying CLI framework (`abscissa`) to version 0.6.0-beta.1,
which now uses `clap` for parsing command line arguments. This substantially improves the UX of the CLI,
by adding support for `--help` flags in subcommands and improving help and usage printouts.

The `--version` option of the `create channel` subcommand has been renamed
to `--channel-version`, with the old name still supported as an alias.
Additionally, the `-h` short flag on many commands is now `-H` to avoid
clashes with the clap-provided short flag for help.

This release also improves the handling of account sequence mismatch errors,
with a recovery mechanism to automatically retry or drop tx upon such errors.

The relayer now also supports dynamic versions in channel open handshake (which is needed by Interchain Accounts), and enables full support for IBC v2.

