# Pre-requisites

## 1. Rust

The IBC Relayer is developed with the [Rust](https://www.rust-lang.org) programming language. In order to build and run the relayer you need to install and configure `Rust` on your machine.

### Fresh Rust installation

For instructions on how to install `Rust` on your machine please follow the official [`Notes about Rust Installation`](https://www.rust-lang.org/tools/install).

The provided instructions will install all the Rust toolchain including `rustc`, `cargo`, and `rustup` that are required to build the project.

### Version requirements

Hermes is developed and tested using the latest version of Rust, `1.60` at
the moment. To check that your toolchain is up-to-date run:

```shell
rustc --version
```

In case you already had installed the Rust toolchain in the past, you can
update your installation by running `rustup update`.

### Testing the installation

After you install the `Rust` toolchain you can execute the following command:

```shell
cargo version
```

This should display the `cargo` version and confirm the proper installation.

## 2. Golang

You will also need the __Go__ programming language installed and configured on your machine. This is a requirement for the the section [Installing Gaia](./tutorials/local-chains/gaia.md) in the [Two Local Chains](./tutorials/local-chains/index.md) tutorial.

To install and configure Golang on your machine please follow the [Golang official documentation](https://golang.org/doc/install).

## Next Steps

Next, go to the [Installation](./installation.md) section to learn how to build Hermes.
