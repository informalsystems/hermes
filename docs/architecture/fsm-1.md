# Connection Handshake FSM


## Input Events:


###### Chain events:

- __OpenInit__
- __OpenTry__
- __OpenAck__
- __OpenConfirm__ (no FSM should be created to handle this event)
- __NewBlock__
- __UpdateClient__


###### Query results:

- __RelayerClientResponse__, parametrized result:
    * if (y), then there is some new headers are available and the client on the opposite chain should be updated
    * if (n), then the client on the opposite chain does not need to be updated


## FSM states:

1. __Z__ = uninitialized
2. __Q[d]__ = querying (fetching) headers from destination chain
3. __Q[s]__ = querying (fetching) headers from source chain
4. __U[s]__ = updating IBC client on source chain with (newer) headers
5. __U[d]__ = updating IBC client on destination chain with (newer) headers
6. __W__ = waiting for new block event (next height) on the source chain
7. __S__ = submitting the datagram + proofs to destination chain
8. __X__ = terminated

Proof-related states:

- __P__ = creating proofs
- __PCC__ = creating the client (or consensus) proof + connection state proof
- __PC__ = creating the connection state proof


## FSM transition table:


| State|           Input        | Next State |  Output  |
|:----:|:----------------------:|:----------:|:--------:|
| Z    | OpenInit \| OpenTry    |   Q[d]     | Query destination chain headers via relayer client |
| Z    | OpenAck |      W     | _ |
| Q[d] | RelayerClientResponse(y)|   U[s]     | Submit UpdateClient on source chain |
| Q[d] | RelayerClientResponse(n)|   W     | _ |
| U[s] | UpdateClient           |   Q[s]     | Query source chain headers via relayer client |
| W    | NewBlock               |   Q[s]     | Query source chain headers via relayer client |
| Q[s] | RelayerClientResponse(y) |   U[d]     | Submit UpdateClient on destination chain |
| Q[s] | RelayerClientResponse(n) |   P     | [internal] Create proofs |
| U[d] | UpdateClient           |    P       | [internal] Create proofs |
| P    | OpenInit \| OpenTry    |   PCC      | Query the IBC client state and the connection state on source chain |
| P    | OpenAck     |    PC      | Query the connection state on source chain |
| PC   | RelayerClientResponse(n) |    S      | Submit datagram + proofs to destination chain |
| PCC  | RelayerClientResponse(n) |    S      | Submit datagram + proofs to destination chain |
|  S   | NewBlock               |   X       | FSM Exit |

## Dependencies:

- Relayer client to destination chain (for state __Q[d]__)
- Relayer client to source chain (for state __Q[s]__)
- Height of source chain
- Height of destination chain
- Height of IBC client on source chain
- Height of IBC client on destination chain
- RPC to destination chain (for states __U[d]__ and __S__ and __PC__ and __PCC__)
- RPC to source chain (for state __U[s]__)

Limitations to this description:

- have to consider height offsets!
- more details about states __PC__ and __PCC__ are needed 