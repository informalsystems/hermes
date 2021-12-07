- The relayer will now avoid submitting a tx after the simulation failed
  (in all but one special case) to avoid wasting fees unnecessarily
  ([#1479](https://github.com/informalsystems/ibc-rs/issues/1479))