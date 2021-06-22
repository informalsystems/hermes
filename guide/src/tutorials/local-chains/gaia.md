# Install Gaia

The script to start the chains requires gaia to be installed.

> __NOTE__: This assumes you have `Golang` programming language installed on 
> your machine. If not, please ensure you install before proceeding. See 
> more details in the [Pre-requisites](../../pre_requisites.md#2-golang) section.

#### Clone gaia

Clone the repository from Github:

```shell
git clone https://github.com/cosmos/gaia.git ~/go/src/github.com/cosmos/gaia
```

#### Build and Install

Run the `make` command to build and install `gaiad`

```shell
cd ~/go/src/github.com/cosmos/gaia
git checkout v4.2.1
make install
```

If the command above is successful you can run the following command to ensure it was properly installed:

```shell
gaiad version --log_level error --long | head -n4
```
Output:
```shell
name: gaia
server_name: gaiad
version: v4.2.1
commit: dbd8a6fb522c571debf958837f9113c56d418f6b
```

## Next Steps

In the next section you will learn how to [start two local chains](./start.md)
