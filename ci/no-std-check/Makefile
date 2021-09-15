check-panic-conflict:
	cargo build \
		--features use-unsupported

check-cargo-build-std:
	rustup run nightly -- \
		cargo build -j1 -Z build-std=core,alloc \
		--features use-unsupported \
		--target x86_64-unknown-linux-gnu

check-wasm:
	rustup run nightly -- \
		cargo build \
		--features use-unsupported \
		--target wasm32-unknown-unknown

check-substrate:
	rustup run nightly -- \
		cargo build \
		--features use-substrate \
		--features use-unsupported \
		--target wasm32-unknown-unknown
