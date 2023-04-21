# Troubleshooting

This section provides guidelines regarding troubleshooting. 

---

## Sections

- **[Help Command][help]**
    * Learn about `hermes help` command, providing a CLI documentation for all `hermes` commands.
- **[Profiling][profiling]**
    * Learn how to `profile` your Hermes binary to identify slow methods and bottlenecks.
- **[Parametrize the log level][log-level]**
    * Learn how to configure the `log-level` to help with debugging.
- **[Patch Gaia][patching]**
    * Learn how to `patch` your local gaia chain(s) to enable some corner-case methods (e.g., channel close).
- **[Inspecting the relayer state][relayer state]**
    * Learn how to `inspect` the state of Hermes.
- **[Cross-stack misconfiguration][cross-stack-config]**
    * Learn how to configure Hermes, Tendermint, and the SDK such that they play well with Hermes.
- **[Genesis restart without IBC upgrade proposal][genesis-restart]**
    * Learn how to update a client after a chain undergoes a genesis restart without an IBC upgrade proposal.

[help]: ./help-command.md
[log-level]: ./log-level.md
[profiling]: ./profiling.md
[patching]: ./patch-gaia.md
[relayer state]: ./inspect.md
[cross-stack-config]: ./cross-comp-config.md
[genesis-restart]: ./genesis-restart.md
