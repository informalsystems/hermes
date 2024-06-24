- Fix a bug where in some cases, Hermes would drop all events in a
  batch that came after an event rejected by the filtering policy
  ([\#4034](https://github.com/informalsystems/hermes/issues/4034))