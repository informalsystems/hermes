# Even more local chains

In this tutorial, you will test Hermes against four chains using Gaiad manager `gm` connected in an arbitrary topology of IBC channels.

Using `gm` you will start four [`gaia`](https://github.com/cosmos/gaia) chains that support the `IBC` protocol.

Make sure that you followed the steps in the [Prerequisites for local chains](../pre-requisites/index.md) section before moving to the [next section](./start-local-chains.md).


---

## Sections

* **[Start Local Chains](./start-local-chains.md)**
    * Start four local chains with `gm` and set up Hermes.

* **[Build the topology](./build-the-topology.md)**
    * Add a relay path between every chain and relay on an arbitrary topology with packet filters.

* **[Start relaying](./start-relaying.md)**
    * Exchange and relay packets between these chains.

* **[Add new instances of Hermes](./concurrent-instances.md)**
    * Add new instances of Hermes to start relaying on the paths filtered out by the first instance.


