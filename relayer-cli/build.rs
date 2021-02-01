fn main() {
    // Overwrites the package `name` to be 'hermes' (the binary name), instead of 'ibc-relayer-cli'
    // (which is the crate name), so that abscissa outputs consistent usage and help messages.
    // https://github.com/informalsystems/ibc-rs/issues/590
    // Note: This can potentially break the normal cargo (or crates.io) workflow.
    println!("cargo:rustc-env=CARGO_PKG_NAME=hermes");
}