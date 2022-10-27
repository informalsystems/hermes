## Install Gaiad Manager

Gaiad manager (`gm`) is a command-line tool (CLI) that helps manage local `gaiad` networks. 

Follow the instructions below to install and configure `gm`.

---

### Requirements
* Bourne shell (`sh`)
* [`sconfig`](https://github.com/freshautomations/sconfig/releases) and
  [`stoml`](https://github.com/freshautomations/stoml/releases) installed in your PATH (put them in `/usr/local/bin`)
* `sed`, `tr`
* For shell-completion Bourne Again Shell (`bash`) for the local user

### How to run

1. Install the dependencies.

    On macOS:
    ```bash
    # You might need sudo permissions and create the `usr/local/bin` directory

    curl -Lo /usr/local/bin/sconfig https://github.com/freshautomations/sconfig/releases/download/v0.1.0/sconfig_darwin_amd64
    curl -Lo /usr/local/bin/stoml https://github.com/freshautomations/stoml/releases/download/v0.7.0/stoml_darwin_amd64
    chmod 755 /usr/local/bin/sconfig
    chmod 755 /usr/local/bin/stoml
    ```
    On Linux:
    ```bash
    curl -Lo /usr/local/bin/sconfig https://github.com/freshautomations/sconfig/releases/download/v0.1.0/sconfig_linux_amd64
    curl -Lo /usr/local/bin/stoml https://github.com/freshautomations/stoml/releases/download/v0.7.0/stoml_linux_amd64
    chmod 755 /usr/local/bin/sconfig
    chmod 755 /usr/local/bin/stoml
    ```

2. Install `gm`

    ```bash
    git clone https://github.com/informalsystems/gm
    gm/bin/gm install
    ```
    Alternatively, you can create the folder `$HOME/.gm/bin` and copy the files from `gm/bin` in there.

3. Activate `gm`
* Add `source $HOME/.gm/bin/shell-support` to a file that executes when a new terminal window comes up
  (`$HOME/.bash_profile` or `$HOME/.bashrc` or `$HOME/.zprofile`)
* (Optional) Enable auto-completion

    - On macOS:

        ```bash
        # Note: zsh is the default shell on MacOS, so no need to run this unless you explicitly use bash
        brew install bash-completion
        ```

    - On Linux:

        ```
        apt install bash-completion || yum install bash-completion
        ```

* Restart your terminal

Note: The `shell-support` script allows bash-completion as well as creating a `gm` alias, so you don't need to add more
entries to your PATH environment variable. If you don't want to use this, you can always just add `$HOME/.gm/bin` to
your path.

### The configuration: `gm.toml`
**Where**: `$HOME/.gm/gm.toml`.

**Description**: This file contains all the high-level node configuration that `gm` is aware of. Note that all entries under `[global]` are also valid entries under any `[node]` header, and can be used to override the global entries for specific nodes/validators.

**Entries**: All entries are defined and documented in the `gm.toml` example configuration file.

Copy and paste below to `$HOME/.gm/gm.toml` and set Hermes' binary path according to your setup.

The following configuration you need to specify 2 `gaiad` chains. `hermes` will know about these chains.

```toml
{{#include ../../templates/files/gm/default_gm.toml}}
```

> __NOTE:__ Go to this page for more details about [Gaiad Manager](https://github.com/informalsystems/gm)

---

## Next steps

Now that `Gaiad Manager` is installed on your machine, visit the [first tutorial](../local-chains/index.md) to learn the basics of Hermes. You will start two local chains and exchange tokens over IBC transfers.
