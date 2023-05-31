- Add two new configurations for the telemetry:
  - `submitted_range` used to specify the range of the histogram
    buckets for the `tx_latency_submitted` metric.
  - `confirmed_range` used to specify the range of the histogram
    buckets for the `tx_latency_confirmed` metric.
  ([#3366](https://github.com/informalsystems/hermes/issues/3366))