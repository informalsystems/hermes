# Install Gaia

The script to start the chains requires gaia to be installed.

#### Clone gaia

Clone the repository from Github:

```shell
git clone https://github.com/cosmos/gaia.git ~/go/src/github.com/cosmos/gaia
```

#### Build and Install

Run the `make` command to build and install `gaiad`

```shell
cd ~/go/src/github.com/cosmos/gaia
git checkout v3.0.0
make install
```

If the command above is successful you can run the following command to ensure it was properly installed:

```shell
gaiad version
```

#### Next Steps

In the next section you will learn how to [start two local chains](./local_chains.md)