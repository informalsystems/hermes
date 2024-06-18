- Remove the `telemetry` and `rest-server` feature flags, ensuring Hermes is always built with telemetry and REST support.
  Both servers can still be disabled in the configuration file, by setting `telemetry.enabled = false` and `rest.enabled = false`, respectively.
  ([\#3878](https://github.com/informalsystems/hermes/pull/3878))
