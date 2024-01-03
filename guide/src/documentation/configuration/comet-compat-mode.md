# CometBFT Compatibility modes

## Overview

There are two different compatibility modes for CometBFT, one for version v0.34 and one for versions v0.37 and v0.38. In order to verify the compatibility used Hermes queries the node's `/status` endpoint, which contains the CometBFT version used. This can be an issue if a chain uses a custom version which does not output the version string Hermes expects. To still be able to relay for these chains a configuration can be set in Hermes.

## Configuration

The configuration is set per chain and can take two values `0.34` and `0.37`, other values will be invalid:

```toml
[[chains]]
...
compat_mode = '0.34'
```

Hermes will act in the following way whether or not the configuration is set:

* `compat_mode` is specified and the version queried from `/status` is the same as the one configured: Use that version without log output
* `compat_mode` is specified but the version queried from `/status` differs: The compatibility mode configured is used, but a warning log is outputted
* `compat_mode` is not specified but /status returns a correct version: The compatibility mode  retrieved from the endpoint is used
* `compat_mode` is not specified and /status does not return a valid version: Hermes stops and outputs an error informing the user that the `compat_mode` needs to be configured

The configuration can also be found in the example [config.toml](https://github.com/informalsystems/hermes/blob/{{#include ../../templates/hermes-version.md}}/config.toml#382)