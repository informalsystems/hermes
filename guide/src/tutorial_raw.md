# Connecting the chains

In the rest of this section we will show how to create the clients, establish a connection and a channel between the two chains, and relay packets over the channel. But first, a note on identifiers.

## Identifiers
A chain allocates identifiers when it creates clients, connections and channels. These identifiers can subsequently be used to refer to existing clients, connections and channels.

Chains allocate identifiers using a chain specific allocation scheme.
Currently, cosmos-SDK implementation uses:
 - `07-tendermint-<n>` for tendermint clients
    - For example `07-tendermint-0` is assigned to the first client created on `ibc-1`:
        ```shell
        hermes tx raw create-client ibc-1 ibc-0 | jq
        ```
        ```json
        {
          "status": "success",
          "result": {
            "CreateClient": {
              "client_id": "07-tendermint-0",
              "client_type": "Tendermint",
              "consensus_height": {
                "revision_height": 294,
                "revision_number": 0
              },
              "height": {
                "revision_height": 286,
                "revision_number": 1
              }
            }
          }
        }
        ```
        We will create a second client on `ibc-1` with identifier `07-tendermint-1` in the client tutorial.

 - `connection-<n>` for connections
     - For example `connection-0` is assigned to the first connection created on `ibc-1`:
         ```shell
         hermes tx raw conn-init ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 | jq
         ```
         ```json
        {
          "status": "success",
          "result": {
            "OpenInitConnection": {
              "client_id": "07-tendermint-0",
              "connection_id": "connection-0",
              "counterparty_client_id": "07-tendermint-0",
              "counterparty_connection_id": null,
              "height": {
                "revision_height": 718,
                "revision_number": 1
              }
            }
          }
        }
         ```
        We will create a second connection on `ibc-1` with identifier `connection-1` in the connection tutorial.

 - `channel-<n>` for channels
     - For example `channel-0` is assigned to the first channel created on `ibc-1`:
          ```shell
          hermes tx raw chan-open-init ibc-1 ibc-0 connection-0 transfer transfer | jq
          ```
          ```json
        {
          "status": "success",
          "result": {
            "OpenInitChannel": {
              "channel_id": "channel-0",
              "connection_id": "connection-0",
              "counterparty_channel_id": null,
              "counterparty_port_id": "transfer",
              "height": {
                "revision_height": 761,
                "revision_number": 1
              },
              "port_id": "transfer"
            }
          }
        }
          ```
        We will create a second channel on `ibc-1` with identifier `channel-1` in the channel tutorial.

In the following tutorials the `ibc-0` and `ibc-1` chains are setup and configured. For clarity, the tutorials run on a setup where the identifiers allocated to the client, connection and channel on `ibc-0` are `07-tendermint-0`, `connection-0` and `channel-0` respectively. Identifiers allocated to the client, connection and channel on `ibc-1` are `07-tendermint-1`, `connection-1` and `channel-1` respectively.

If you want to ensure you get the same identifiers while following the tutorial, run the above three commands once on `ibc-1` before going over the next sections.

## Steps to start relaying packets between the two local chains

In order to start relaying packets please follow the steps below:

* [Configure Clients](./tutorial_client_raw.md)

* [Connection Handshake](./tutorial_conn_raw.md)

* [Open the Channel](./tutorial_chan_open_raw.md)

* [Relay Packets](tutorial_packet_raw.md)
