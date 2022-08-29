# Inspecting the relayer state

To get some insight into the state of the relayer,
Hermes will react to a `SIGUSR1` signal by dumping its state to
the console, either in plain text form or as a JSON object if Hermes
was started with the `--json` option.

To send a `SIGUSR1` signal to Hermes, look up its process ID (below PID)
and use the following command:

```shell
kill -SIGUSR1 PID
```

Hermes will print some information about the workers which are currently running.

For example, with three chains configured and one channel between each pair of chains:

```text
INFO Dumping state (triggered by SIGUSR1)
INFO
INFO * Chains: ibc-0, ibc-1, ibc-2
INFO * Client workers:
INFO   - client::ibc-0->ibc-1:07-tendermint-0 (id: 5)
INFO   - client::ibc-0->ibc-2:07-tendermint-0 (id: 9)
INFO   - client::ibc-1->ibc-0:07-tendermint-0 (id: 1)
INFO   - client::ibc-1->ibc-2:07-tendermint-1 (id: 11)
INFO   - client::ibc-2->ibc-0:07-tendermint-1 (id: 3)
INFO   - client::ibc-2->ibc-1:07-tendermint-1 (id: 7)
INFO * Packet workers:
INFO   - packet::channel-0/transfer:ibc-0->ibc-1 (id: 2)
INFO   - packet::channel-0/transfer:ibc-1->ibc-0 (id: 6)
INFO   - packet::channel-0/transfer:ibc-2->ibc-0 (id: 10)
INFO   - packet::channel-1/transfer:ibc-0->ibc-2 (id: 4)
INFO   - packet::channel-1/transfer:ibc-1->ibc-2 (id: 8)
INFO   - packet::channel-1/transfer:ibc-2->ibc-1 (id: 12)
```

or in JSON form (prettified):

```json
{
  "timestamp": "Jul 12 17:04:37.244",
  "level": "INFO",
  "fields": {
    "message": "Dumping state (triggered by SIGUSR1)"
  }
}
{
  "chains": [
    "ibc-0",
    "ibc-1",
    "ibc-2"
  ],
  "workers": {
    "Client": [
      {
        "id": 5,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-1",
          "dst_client_id": "07-tendermint-0",
          "src_chain_id": "ibc-0"
        }
      },
      {
        "id": 9,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-2",
          "dst_client_id": "07-tendermint-0",
          "src_chain_id": "ibc-0"
        }
      },
      {
        "id": 1,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-0",
          "dst_client_id": "07-tendermint-0",
          "src_chain_id": "ibc-1"
        }
      },
      {
        "id": 11,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-2",
          "dst_client_id": "07-tendermint-1",
          "src_chain_id": "ibc-1"
        }
      },
      {
        "id": 3,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-0",
          "dst_client_id": "07-tendermint-1",
          "src_chain_id": "ibc-2"
        }
      },
      {
        "id": 7,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-1",
          "dst_client_id": "07-tendermint-1",
          "src_chain_id": "ibc-2"
        }
      }
    ],
    "Packet": [
      {
        "id": 2,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-1",
          "src_chain_id": "ibc-0",
          "src_channel_id": "channel-0",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 6,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-0",
          "src_chain_id": "ibc-1",
          "src_channel_id": "channel-0",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 10,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-0",
          "src_chain_id": "ibc-2",
          "src_channel_id": "channel-0",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 4,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-2",
          "src_chain_id": "ibc-0",
          "src_channel_id": "channel-1",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 8,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-2",
          "src_chain_id": "ibc-1",
          "src_channel_id": "channel-1",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 12,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-1",
          "src_chain_id": "ibc-2",
          "src_channel_id": "channel-1",
          "src_port_id": "transfer"
        }
      }
    ]
  }
}
```