- Fix bug where one could sometimes not subscribe to events.
  This mostly affected the `listen` command but also external
  consumers of events via the `EventMonitor` interface
  ([\#3070](https://github.com/informalsystems/hermes/issues/3070))