- Added a new Prometheus metric `simulate_errors` for tracking when a transaction simulation fails, with the following labels: 
  * `recoverable` (can the execution continue if this happened?) 
  * `account` (account from which the tx was sent) 
  * `error_description` (description of the error) 
  ([\#3845](https://github.com/informalsystems/hermes/issues/3845))

  ```
  # HELP simulate_errors_total Number of errors observed by Hermes when simulating a Tx
  # TYPE simulate_errors_total counter
  simulate_errors_total{account="osmo17ndx5qfku28ymxgmq6zq4a6d02dvpfjjul0hyh",error_description="Unknown error",recoverable="false",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 4
  ```
