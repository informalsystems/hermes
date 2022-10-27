- Added a new optional flag, `--denom` to the `hermes keys balance` command in order
  to specify for which denomination the balance is queried. A special
  value, `all`, can be used to query the balance for all denominations
  ([#2726](https://github.com/informalsystems/ibc-rs/issues/2726))