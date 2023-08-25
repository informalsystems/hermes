This release of Hermes notably features a new pull-based event source which fetches events from the chain periodically using
the `/block_results` RPC endpoint instead of getting them over WebSocket.
    
To use the new pull-based event source, set 

```toml
event_source = { mode = 'pull', interval = '1s' }`
```

in the per-chain configuration.

### Note for operators

> ⚠️  Be aware that this release contains breaking changes to the Hermes configuration.
> ⚠️  Please consult the [`UPGRADING.md`](UPGRADING.md) document for more details.

