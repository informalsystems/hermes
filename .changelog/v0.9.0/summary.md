*November 23rd, 2021*

> This release honors Anca Zamfir, who has lead ibc-rs from its inception and through its first two years of life.
> The whole team is grateful for her dedication and the nurturing environment she created.
> To many more achievements, Anca!! 🥂

#### Notice for operators

This release requires operators to update their Hermes configuration.
The `mode` configuration section now replaces the `strategy` option.

##### `strategy = 'packets'`

If Hermes was configured with `strategy = 'packets'`, then the configuration needs to be changed in the following way:

```diff
 [global]
-strategy = 'packets'
 log_level = 'trace'
-clear_packets_interval = 100
-tx_confirmation = true
+
+[mode]
+
+[mode.clients]
+enabled = true
+refresh = true
+misbehaviour = true
+
+[mode.connections]
+enabled = false
+
+[mode.channels]
+enabled = false
+
+[mode.packets]
+enabled = true
+clear_interval = 100
+clear_on_start = true
+filter = false
+tx_confirmation = true
```

##### `strategy = 'all'`

If Hermes was configured to complete connection and channel handshakes as well, ie. with `strategy = 'all'`,
then on top of the changes above, `mode.connections.enabled` and `mode.chhanels.enabled` must be set to `true`.

[See the relevant section][config-mode-toml] of the documented `config.toml` file in the repository for more details.

[config-mode-toml]: https://github.com/informalsystems/ibc-rs/blob/v0.9.0/config.toml#L9-L59

