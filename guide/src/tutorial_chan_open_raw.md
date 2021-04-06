# 3. Channel Handshake

### 3.1 chan-open-init

Initialize a new unordered channel on `ibc-0`:
```shell
hermes tx raw chan-open-init ibc-0 ibc-1 connection-0 transfer transfer -o UNORDERED
```

### 3.2 chan-open-try

Send a channel open try to `ibc-1`:
```shell
hermes tx raw chan-open-try ibc-1 ibc-0 connection-1 transfer transfer -s channel-0
```

Take note of the ID allocated by the chain, e.g. `channel-1` on `ibc-1`. Use in the `chan-open-ack` CLI

### 3.3 chan-open-ack

Send a channel open acknowledgment to `ibc-0`:
```shell
hermes tx raw chan-open-ack ibc-0 ibc-1 connection-0 transfer transfer -d channel-0 -s channel-1
```
Note that, in order use a channel with index 1 on ibc-1 in the handshake, prior to execute the channel handshake 
decribe here run 
```hermes tx raw chan-open-init ibc-1 ibc-0 connection-1 transfer transfer -o UNORDERED```,  
otherwise the counter for channels of ibc-0 starts at zero and the counter party of channel-0 on ibc-0 is channel-0 on ibc-1 
(created by ```chan-open-try ibc-1 ibc-0```).  
### 3.4 chan-open-confirm

Send the open confirmation to `ibc-1`:
```shell
hermes tx raw chan-open-confirm ibc-1 ibc-0 connection-1 transfer transfer -d channel-1 -s channel-0
```

### 3.5 query channel
To verify that the two ends are in `Open` state:

```shell
hermes query channel end ibc-0 transfer channel-0
```

```shell
hermes query channel end ibc-1 transfer channel-1
```

## Next Steps

In the next section, we'll start to [relay packets](./tutorial_packet_raw.md)