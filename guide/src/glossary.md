# Glossary

These are some of the definitions used in this guide: 

| Term | Definition |
|------|------------|
|IBC transaction| A transaction that includes IBC datagrams (including packets). This is constructed by the relayer and sent over the physical network to a chain according to the chain rules. For example, for tendermint chains a broadcast_tx_commit request is sent to a tendermint RPC server.|
|IBC datagram| An element of the transaction payload sent by the relayer; it includes client, connection, channel and IBC packet data. Multiple IBC datagrams may be included in an IBC transaction.|
|IBC packet| A particular type of IBC datagram that includes the application packet and its commitment proof.|
|IBC Client| Client code running on chain, typically only the light client verification related functionality.|
|Relayer Light Client| Full light client functionality, including connecting to at least one provider (full node), storing and verifying headers, etc.|
|Source chain| The chain from which the relayer reads data to fill an IBC datagram.|
|Destination chain| The chain where the relayer submits transactions that include the IBC datagram.|

