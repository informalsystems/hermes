- Add a global flag `--debug` which can take one or more of the following values, separated by commas:
  - `rpc`: show RPC debug logs
  - `profiling`: show profiling information in the console
  - `profiling-json`: dump the profiling information to a JSON file in the directory specified in `PROFILING_DIR` env variable if present, or the current directory otherwise.
  ([#2852](https://github.com/informalsystems/hermes/issues/2852))