# Telemetry

To gain a better understanding of the status and activity of the relayer,
Hermes features a built-in telemetry service based on the [OpenTelemetry][opentelemetry] observability framework,
whose metrics can be exposed over HTTP for integration with the [Prometheus][prometheus] monitoring system.

The official Hermes builds for Linux and macOS come with telemetry support since version `v0.4.0`.
See the [installation instructions][installation] for how to obtain the latest version of Hermes.

## Configuration

The telemetry service is not active by default, and must be enabled in the relayer configuration:

```toml
[telemetry]
enabled = true          # default = false
host    = '127.0.0.1'   # default value
port    = 3001          # default value
```

Please see the [relevant section for *Configuration*](../configuration/index.md) for more general details about Hermes configuration options.

[installation]: ../../quick-start/installation.md#install-the-relayer
[opentelemetry]: https://opentelemetry.io
[prometheus]: https://prometheus.io
