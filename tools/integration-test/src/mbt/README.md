# MBT for Hermes Integration Test

Make sure [`apalache-mc`](https://github.com/informalsystems/apalache) is installed and setup properly. Check `apalache-mc version`.

```bash
git checkout rnbguy/integration-test/mbt
cargo test -p ibc-integration-test --features mbt mbt::transfer
```
