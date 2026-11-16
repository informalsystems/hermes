#!/usr/bin/env bash
set -euo pipefail
recipe=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$1"
out=$(cd "$1" && pwd)
for item in \
  tendermint:fc997743ecfd4864bbca8170d68d9b2bee24653b034210752c2d883ef4b838b1 \
  tendermint-proto:d2c40e13d39ca19082d8a7ed22de7595979350319833698f8b1080f29620a094
do
    crate=${item%:*}
    checksum=${item#*:}
    release="$crate-0.40.4"
    test ! -e "$out/$release"
    curl -fsSL "https://static.crates.io/crates/$crate/$release.crate" -o "$out/$release.crate"
    python3 - "$out/$release.crate" "$checksum" <<'PY'
import hashlib,sys
with open(sys.argv[1],"rb") as f:
    assert hashlib.sha256(f.read()).hexdigest() == sys.argv[2], "crate checksum mismatch"
PY
    tar -xzf "$out/$release.crate" -C "$out"
    (cd "$out/$release" && git apply "$recipe/$release-ml-dsa.patch")
done
python3 - "$out" <<'PY'
from pathlib import Path
import json,sys
root=Path(sys.argv[1])
out=['[patch.crates-io]']
for name in ('tendermint','tendermint-proto'):
    out.append(f'{name} = {{ path = {json.dumps(str(root/f"{name}-0.40.4"))} }}')
(root/'rust-patches.toml').write_text('\n'.join(out)+'\n')
PY
