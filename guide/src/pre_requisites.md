# Pre-requisites

## 1. Rust

The IBC Relayer is developed with the [Rust]() programming language. In order to build and run the relayer you need to install and configure `Rust` in your machine.

For instructions on how to install `Rust` on your machine please follow their official [`Notes about Rust Installation`](https://www.rust-lang.org/tools/install). 

The provided instructions will install all the Rust toolchain including `rustc`, `cargo`, and `rustup` that are required to build the project.

### Testing the installation

After you install the `Rust` toolchain you can execute the following command:

```shell
cargo version
```

This should display the `cargo` version and confirm the proper installation.

## 2. Golang

You will also need the __Go__ programming language installed and configured in your machine. This is a requirement for the the section [Installing Gaia](./gaia.md) in the [Two Local Chains](./two_chains.md) tutorial. 

To install and configure Golang in your machine please follow the [Golang official documentation](https://golang.org/doc/install)

## Next Steps

Next, go to the [Setup](./setup.md) section to learn how to build the relayer.