NIGHTLY_VERSION=nightly-2021-09-01

setup:
	rustup install $(NIGHTLY_VERSION)
	rustup target add wasm32-unknown-unknown --toolchain $(NIGHTLY_VERSION)

check-panic-conflict:
	cargo build \
		--no-default-features \
		--features use-ibc,use-unsupported

check-cargo-build-std:
	rustup run $(NIGHTLY_VERSION) -- \
		cargo build -Z build-std=core,alloc \
		--features use-ibc,use-unsupported \
		--target x86_64-unknown-linux-gnu

check-wasm:
	rustup run $(NIGHTLY_VERSION) -- \
		cargo build \
		--features use-ibc,use-unsupported \
		--target wasm32-unknown-unknown

check-substrate:
	rustup run $(NIGHTLY_VERSION) -- \
		cargo build \
		--no-default-features \
		--features use-ibc,use-unsupported,use-substrate \
		--target wasm32-unknown-unknown
