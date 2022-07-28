
# End-to-end tests for Hermes

This folder contains end-to-end tests for Hermes, written in Python.

Unlike the Rust-based integration tests which hook into the relayer API,
this test suite calls the `hermes` binary for setting up clients,
connections and channels, and perform token transfers.

## Usage

To run the end-to-end tests defined in this folder, run the following
command from the root of the repository:

```bash
$ cargo test -p ibc-integration-test -- python_end_to_end_tests
```

