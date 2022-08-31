# Install Gaia

For `gm` to start the chains, it requires `Gaia` to be installed.

> __NOTE__: This assumes you have `Golang` programming language installed on 
> your machine. If not, please ensure you install before proceeding. See 
> more details in the [Pre-requisites](../../quick-start/pre-requisites.md#2-golang) section.

Follow the instructions below to install `Gaia`.

---

#### Clone Gaia

Clone the repository from GitHub:

```shell
{{#template ../../templates/commands/git/gaia}} ~/go/src/github.com/cosmos/gaia
```

#### Build and Install

Run the `make` command to build and install `gaiad`

```shell
cd ~/go/src/github.com/cosmos/gaia
git checkout v4.2.1 
make install
```

>__NOTE__: Specific to M1 macOS, there could be some warnings after running `make install` which can be safely ignored as long as `gaiad` binaries are built in `$HOME/go/bin` directory.
><br /><br />Add the path `export PATH=$HOME/go/bin:$PATH`

If the command is successful, you can run the following command to ensure it was properly installed:

```shell
{{#template ../../templates/commands/gaia/version}}
```

Output:
```shell
name: gaia
server_name: gaiad
version: v4.2.1
commit: dbd8a6fb522c571debf958837f9113c56d418f6b
```

---

## Next Steps

Go to the [next section](./gaiad-manager.md) to install `gm`, a tool to easily start IBC-enabled local chains.