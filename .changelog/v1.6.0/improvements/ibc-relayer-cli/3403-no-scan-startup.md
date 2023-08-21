- By disabling clients, connections and channels workers, and setting
  `clear_on_start` to `false`, Hermes will now skip the scanning phase
  during startup, significantly improve startup time when relaying on chains
  with hundreds or thousands of open channels, connections and/or clients.
  See the [Performance tuning][perf-tuning] page of the guide for more information.
  ([\#3403](https://github.com/informalsystems/hermes/issues/3403))

[perf-tuning]: https://hermes.informal.systems/documentation/configuration/performance.html#3-slow-start
