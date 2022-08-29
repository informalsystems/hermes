# Install Gaia

For `gm` to start the chains, it requires Gaia to be installed.

> __NOTE__: This assumes you have `Golang` programming language installed on 
> your machine. If not, please ensure you install before proceeding. See 
> more details in the [Pre-requisites](../../quick-start/pre-requisites.md#2-golang) section.

#### Clone Gaia

Clone the repository from GitHub:

```shell
git clone https://github.com/cosmos/gaia.git ~/go/src/github.com/cosmos/gaia
```

#### Build and Install

Run the `make` command to build and install `gaiad`

```shell
cd ~/go/src/github.com/cosmos/gaia
git checkout <latest-release-tag> 
make install
```
> Find the [latest-release-tag](https://github.com/cosmos/gaia/releases) here.

>__NOTE__: Specific to M1 macOS, there could be some warnings after running `make install` which can be safely ignored as long as `gaiad` binaries are built in `$HOME/go/bin` directory.
><br /><br />Add the path `export PATH=$HOME/go/bin:$PATH`

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
