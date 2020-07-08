# Connection Handshake FSM


## Input Events:


###### Chain events:

- __OpenInit__
- __OpenTry__
- __OpenAck__
- __OpenConfirm__
- __NewBlock__
- __UpdateClient__


###### Query results:

- __RelayerClientResponse__


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
| Z    | OpenAck \| OpenConfirm |      W     | _ |
| Q[d] | RelayerClientResponse  |   U[s]     | UpdateClient on source chain |
| U[s] | UpdateClient           |   Q[s]     | _ |
| W    | NewBlock               |   Q[s]     | Query source chain headers via relayer client |
| Q[s] | RelayerClientResponse  |   U[d]     | UpdateClient on destination chain |
| U[d] | UpdateClient           |    P       | [internal] Create proofs |
| P    | OpenInit \| OpenTry    |   PCC      | Query the IBC client state and the connection state on source chain |
| P    | OpenInit \| OpenTry \| OpenAck \| OpenConfirm    |    PC      | Query the connection state on source chain |
| PC   | RelayerClientResponse  |    S      | Submit datagram + proofs to destination chain |
| PCC  | RelayerClientResponse  |    S      | Submit datagram + proofs to destination chain |
|  S   | NewBlock               |   X       | FSM Exit |

## Dependencies:

- Relayer client to destination chain (for state __Q[d]__)
- Relayer client to source chain (for state __Q[s]__)
- Height of source chain
- Height of destination chain
- Height of IBC client on source chain
- Height of IBC client on destination chain
- RPC to destination chain (for state __U[d]__)
- RPC to source chain (for state __U[s]__)

Limitations to this description:

- this is a sequential description
- have to consider height offsets!