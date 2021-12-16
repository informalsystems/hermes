- Remove `Timestamp` API that depended on the `chrono` crate:
  ([#1665](https://github.com/informalsystems/ibc-rs/pull/1665)):
  - `Timestamp::from_datetime`; use `From<tendermint::Time>`
  - `Timestamp::as_datetime`, superseded by `Timestamp::into_datetime`
