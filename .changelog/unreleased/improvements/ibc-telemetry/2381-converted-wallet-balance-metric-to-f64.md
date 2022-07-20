- Updated telemetry metric `wallet_balance` to f64 and removed downscaling
  displayed value. Please note that when converting the balance to f64 a loss in
  precision might be introduced in the displayed value.
  ([#2381](https://github.com/informalsystems/ibc-rs/issues/2381))