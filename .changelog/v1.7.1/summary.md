This patch release of Hermes now allows operators to set the clearing interval
at a different value for each chain, using the new per-chain `clear_interval` setting.
The global `clear_interval` setting is used as a default value if the per-chain
setting is not defined.

Additionally, operators can now override the CometBFT compatibility mode to be used
for a chain by using the new `compat_mode` per-chain setting. The main use case for this
is to override the automatically detected compatibility mode in case Hermes gets it wrong
or encounters a non-standard version number and falls back on the wrong CometBFT version.

On top of that, Hermes will now attempt to save on fees by not building a client update
for a given height if the consensus state for that height is already present on chain.
