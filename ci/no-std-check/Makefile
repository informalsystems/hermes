NIGHTLY_VERSION=nightly-2021-09-01

setup:
	rustup install $(NIGHTLY_VERSION)
	rustup target add wasm32-unknown-unknown --toolchain $(NIGHTLY_VERSION)

check-panic-conflict:
	cargo build \
		--no-default-features

check-cargo-build-std:
	rustup run $(NIGHTLY_VERSION) -- \
		cargo build -Z build-std=core,alloc \
		--target x86_64-unknown-linux-gnu

check-wasm:
	rustup run $(NIGHTLY_VERSION) -- \
		cargo build \
		--target wasm32-unknown-unknown

check-substrate:
	rustup run $(NIGHTLY_VERSION) -- \
		cargo build \
		--no-default-features \
		--features use-substrate \
		--target wasm32-unknown-unknown
