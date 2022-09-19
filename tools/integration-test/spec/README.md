# ICS20 Specification

Add desired `Invariant` predicate in `MC_Transfer.tla`. Then execute,

```sh
apalache check --inv=Invariant --run-dir=run MC_Transfer.tla
```

Provided invariants to pass,

```
LocalTransferInv
RestoreRelayInv
InterruptRelayInv
IBCTransferSendPacketInv
IBCTransferReceivePacketInv
IBCTransferAcknowledgePacketInv
IBCTransferTimeoutPacketInv
```

```sh
apalache check --inv=IBCTransferAcknowledgePacketInv --run-dir=run MC_Transfer.tla
```
