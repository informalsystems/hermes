- Updated the channel and port filter parsing to ignore whitespaces.
  This will prevent unintended channel scanning due to accidental
  whitespaces when exact matches are specified in the `packet_filter`
  configuration.
  ([\#4045](https://github.com/informalsystems/hermes/issues/4045))