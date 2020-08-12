# Connection Handshake FSM
A description of the connection datagram builder FSM for a relayer using async operations for queries and light client header fetching is presented.
It has explicit states while async operations are in progress and can therefore act on events while in these states.

A connection FSM is instantiated by the relayer's event handler when a connection event is received. The FSM will either successfully build and submit a connection message or it will exit. 

The connection builder FSM is removed by the event handler upon receiving of an invalidating event. For example an active FSM for `MsgConnOpenTry` is removed if the event handler receives a `ConnOpenTry` event for that connection. This document does not detail the event handler's actions.

## FSM states:
1. __Z__ = uninitialized
2. __FH[d]__ = fetching headers from destination chain
3. __FH[s]__ = fetching headers from source chain
4. __W__ = waiting for new block event (next height) on the source chain
5. __Q__ = querying connection and consesus state, with proofs, on source chain and connection on destination chain
6. __X__ = terminated

There is a timer associated with the FSM state, when it fires the FSM terminates. These transitions from * to X are not shown.

## Input Events:

#### Chain events:

Trigger event is a connection event that occurred at height `ha` and that requires a new datagram to be built:
- __OpenInit(ha)__ - results in building and submitting a `MsqOpenTry` datagram
- __OpenTry(ha)__ - results in building and submitting a `MsqOpenAck` datagram
- __OpenAck(ha)__ - results in building and submitting a `MsqOpenConfirm` datagram

The other chain events the FSM may act upon are:
- __NewBlock(A, ha)__
- __UpdateClient(X, cl_h, hx)__ - client on X was updated with consensus state at height cl_h. The update happened in block with height hx on X.

#### Query events:

- __LCResp__, parametrized result:
    * if (hs), then there are new headers (hs) available and, the client on the opposite chain should be updated
    * if (err), then local light client failed to fetch headers

- __ChainQueryResponse__, parametrized result:
    * if (resp), then a query response is received
    * if (err), then the query failed or timed out (TODO - errors and timeouts may need to be handled differently)

## Conditions
- Req_U[A] = update of IBC B-client on chain A is required, true if latest consensus height of IBC B-client on A is more than N blocks behind (N=100) compared to latest on B.
Note: with the event driven relayer, the `UpdateClient` events update local state of clients, therefore there is no query required.

- Pending_Q = queries are pending, true if not all query responses have been received, false otherwise. The FSM keeps track of queries that were sent and responses that were received. There is a maximum of 3 queries performed by the connection FSM, one for the connection on the destination chain, and two for the source chain (client consensus and connection). These queries are sent in the same time and then the FSM waits for all responses. Some optimizations may be done.

## FSM actions:

Async (light client requests and queries):
 - get_min_set(X, hx) - fetch chain X headers via relayer light client. `hx` is typically the latest height on B. The relayer keeps track of latest chain heights via the `NewBlock` events, therefore no query is required.
 - query(A, B) - send required queries to source and destination chains.

Sync (transaction submission) calls, use `broadcast_tx_commit()` blocking until the result is known:
 - update_client(X, hs) - submit UpdateClient datagram(s) for headers in `hs` to chain X. 
 - conn_open_datagram(X) - verify connection ends and proofs and submit `ConnOpen..` datagram to chain X. The concrete datagram to be submitted depends on the trigger event and connection information.

 Note: the async version can also be used and wait for confirmation via IBC events
 
## FSM transition table:

|State  | Input Event                  | Condition   |  Action                      | Next State    |  Comment  |
|:------|:-----------------------------|:------------|:-----------------------------|:--------------|:----------|
| Z     | OpenInit(ha), OpenTry(ha)    |  Req_U[A]   | get_min_set(B,hb)            | FH[B]         |           |
| Z     | OpenInit(ha), OpenTry(ha)    | ~Req_U[A]   | _                            | W             |           |  
| Z     | OpenAck(ha)                  |             | _                            | W             |           |
| FH[B] | LCResp([..,hb])              |             | err=update_client(A,[..,hb]) | FH[A] or FH[B] | retry on error         |
| FH[B] | LCResp(err)                  |             | _                            | X             |           |
| FH[B] | UpdateClient(A, cl_hB, hA)   | cl_hB >= hb | -                            | FH[A]         | another relayer has updated the client |
| W     | NewBlock(A, hA)              | Req_U[B]    | get_min_set(A,hA)            | FH[A]         |           |
| FH[A] | LCResp([.., hA])             |             | err=update_client(B,[..,hA]) | FH[B] or FH[A] | retry on error 
| FH[A] | LCResp(err)                  |             | _                            | X             |           |
| FH[A] | UpdateClient(B, cl_hA, hB)   | cl_hA >= hA | query(A, B)                  | Q             | another relayer has updated the client |
| Q     | ChainQueryResponse(resp)     |Pending_Q    | _                            | Q             |
| Q     | ChainQueryResponse(resp)     |~Pending_Q   | err=conn_open_datagram(B)    | X             |           |


