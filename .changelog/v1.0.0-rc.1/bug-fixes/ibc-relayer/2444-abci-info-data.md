- Fix a bug where the relayer would fail to relay any packets when the
  `/acbi_info` endpoint of a chain did not include `data` and `version` fields
  ([#2444](https://github.com/informalsystems/ibc-rs/issues/2444))