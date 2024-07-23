- Improve the `excluded_sequences` configuration so that it now accepts
  ranges of sequence values in addition to exact values.
  Accepted format:
    * Exact sequence, e.g. [1, 2, 3]
    * "-" separator, e.g. ["1-3"]

  These can be combined making the following configurations equivalent:
    * `excluded_sequences = { 'channel-0' = [1, "3-5", 7, "9-12"] }`
    * `excluded_sequences = { 'channel-0' = [1, 3, 4, 5, 7, 9, 10, 11, 12] }`

  ([\#4047](https://github.com/informalsystems/hermes/issues/4047))