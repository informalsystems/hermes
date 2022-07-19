- Added a new configuration, `wallet_metric_scale`, to `config.toml` to specify the
  value used to scale down the `wallet_balance` displayed in the telemetry metrics
  in case the raw value does not fit into a unsigned 64-bits integer,
  eg. because the relayer wallet contains a high amount of coins.
  ([#2381](https://github.com/informalsystems/ibc-rs/issues/2381))