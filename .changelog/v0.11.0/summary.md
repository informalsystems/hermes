This release notably speeds up the startup time of Hermes,
adds options to the `create client` command to customize the client parameters,
makes the deposit denomination configurable in `tx raw upgrade-chain` via a new `--denom` flag,
and adds a `completions` CLI command to generate shell auto-completion scripts.

### Note for operators

This release includes a breaking change, which requires the configuration file to be edited.
The `mode.packets.filter` configuration option has been removed and is now enabled by default.

Before running Hermes v0.11.0, make sure you remove the `mode.packets.filter` option from the configuration file.

```diff
--- a/config.toml
+++ b/config.toml
@@ -50,18 +50,6 @@ clear_interval = 100
 # Whether or not to clear packets on start. [Default: false]
 clear_on_start = true

-# Enable or disable the filtering mechanism.
-# Valid options are 'true', 'false'.
-# Currently Hermes supports two filters:
-# 1. Packet filtering on a per-chain basis; see the chain-specific
-#   filter specification below in [chains.packet_filter].
-# 2. Filter for all activities based on client state trust threshold; this filter
-#   is parametrized with (numerator = 1, denominator = 3), so that clients with
-#   thresholds different than this will be ignored.
-# If set to 'true', both of the above filters will be enabled.
-# [Default: false]
-filter = false
-
 # Toggle the transaction confirmation mechanism.
 # The tx confirmation mechanism periodically queries the `/tx_search` RPC
 # endpoint to check that previously-submitted transactions
```

