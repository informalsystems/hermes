# Relayer Specification

Relayers are processes that provide connection layer of the IBC protocol. In the IBC protocol, on chain
modules do not have a way of directly sending a message to each other; this is the responsibility of relayer
processes. Modules signal its intention to send a message by writing data in its data store at the
defined location, and make those data (with corresponding proofs) available to external parties.
Relayer processes read (we say also scan) the state of each chain, construct appropriate IBC datagrams,
verify the corresponding proofs and submit valid datagrams to destination chain.   
We assume existence of multiple relayers, where some relayers could be faulty (behave arbitrarily),
but there is always at least a single correct relayer. We don't make assumptions on the maximum number of 
faulty relayers.

For the purpose of this specification we assume existence of two on chain modules A and B, that executes
IBC protocol. We say that a module A (or B) sends an IBC datagram m to a module B (or A) when a correct
relayer can construct valid datagram m by scanning the state of the chain A. We say that a module A receives
an IBC datagram m, when m was processed by the module A on chain. We assume that modules
are correct.    

Correct relayers need to ensure the following properties:

**[ICS18-Delivery]**: If a module A sends an IBC datagram m to a module B, then m is
eventually received by the module B.

**[ICS18-Validity]**: If a module B receives an IBC datagram m from a module A, 
then m was sent by the module A to the module B.

## System model

We assume that a correct relayer operates in the following model:

### Connected chains

Relayer transfers data between two chains: chainA and chainB. For simplicity, we assume Tendermint chains. 
Each chain operates under Tendermint security model:
- given a block b at height h committed at time `t = b.Header.Time`, `+2/3` of voting power behaves correctly
at least before `t + UNBONDING_PERIOD`, where `UNBONDING_PERIOD` is a system parameter (typically order of weeks).
Validators sets can be changed in every block, and we don't assume any constraint on the way validators are changed
(application specific logic).  

Furthermore, we assume that blockchain applications that operate on top of chainA and chainB writes
relevant data into Merkleised data store (for example IBC packets), and that parts of the store are publicly
available (so relayers can access it). 

In order to access IBC relevant data, a relayer needs to establish connections with full nodes (correct) from 
both chains. Note that there is no constrain on number of faulty full nodes: we can only assume that a correct relayer
will eventually have access to a correct full node. 

### Data availability

Note that data written to a store at height *h* as part of executing block *b* (`b.Height = h`) is effectively committed by 
the next block (at height h+1). The reason is the fact that the data store root hash as an effect of executing block at 
height h is part of the block header at height h+1. Therefore, data read at height h is available until time 
`t = b.Header.Time + UNBONDING_PERIOD`, where `b.Header.Height = h+1`. After time *t* we cannot trust that data anymore.
Note that data present in the store are re-validated by each new block: data added/modified at block *h* are still 
valid even if not altered after, as they are still "covered" by the root hash of the store. 

Therefore UNBONDING_PERIOD gives absolute time bound during which relayer needs to transfer data read at source chain
to the destination chain. As we will explain below, due to fork detection and accountability protocols, the effective 
data availability period will be shorter than UNBONDING_PERIOD. 

### Data verification

As connected chains in IBC do not blindly trust each other, data coming from the opposite chain must be verified at
the destination before being acted upon. Data verification in IBC is implemented by relying on the concept of light client.
Light client is a process that by relying on an initial trusted header (subjective initialisation), verifies and maintains 
set of trusted headers. Note that a light client does not maintain full blockchain and does not execute (verify) application
transitions. It operates by relying on the Tendermint security model, and by applying header verification logic that operates
only on signed headers (header + corresponding commit). 

More details about light client assumptions and protocols can be found 
[here](https://github.com/tendermint/spec/tree/master/rust-spec/lightclient). For the purpose of this document, we assume
that a relayer has access to the light client node that provides trusted headers.
Given a data d read at a given path at height h with a proof p, we assume existence of a function 
`VerifyMembership(header.AppHash, h, proof, path, d)` that returns `true` if data was committed by the corresponding
chain at height *h*. The trusted header is provided by the corresponding light client. 
  
## Relayer algorithm

The main relayer event loop is a pipeline of four stages. Assuming some IBC event at height `h` on `chainA`, 
the relayer:

1. Determines destination chain (`chainB`)
2. Updates (on `chainB`) the IBC client for `chainA` to a certain height `H` where `H >= h+1`.
3. Creates IBC datagram at height `H-1`.
4. Submits the datagram from stage (2) to `chainB`.

Note that an IBC event at height `h` corresponds to the modifications to the data store made as part of executing
block at height `h`. The corresponding proof (that data is indeed written to the data store) can be verified using
the data store root hash that is part of the header at height `h+1`.

Once stage 2 finishes correctly, stage 3 should succeed assuming that `chainB` has not already processed the event. The 
interface between stage 2 and stage 3 is just the height `H`. Once stage 3 finishes correctly, stage 4 should 
succeed. The interface between stage 3 and stage 4 is an IBC datagram.

We assume that the corresponding light client is correctly installed on each chain.

Data structures and helper function definitions are provided 
[here](https://github.com/informalsystems/ibc-rs/blob/master/docs/spec/relayer/Definitions.md). 

```golang
func handleEvent(ev, chainA) Error {
    // NOTE: we don't verify if event data are valid at this point. We trust full node we are connected to
    // until some verification fails. 
    
    // Stage 1.
    // Determine destination chain
    chainB, error = getDestinationInfo(ev, chainA) 
    if error != nil { return error }  

    // Stage 2.
    // Update on `chainB` the IBC client for `chainA` to height `>= targetHeight`.
    targetHeight = ev.height + 1
    // See the code for `updateIBCClient` below.
    proofHeight, error := updateIBCClient(chainB, chainA, targetHeight)
    if error != nil { return error }

    // Stage 3.
    // Create the IBC datagrams including `ev` & verify them.
    datagram, error = CreateDatagram(ev, chainA, chainB, proofHeight)
    if error != nil { return error }
    
    // Stage 4.
    // Submit datagrams.
    error = Submit(chainB, datagram)
    if error != nil { return error }      
}

func getDestinationInfo(ev IBCEvent, chain Chain) (Chain, Error) {
    switch ev.type {
        case SendPacketEvent: 
            chainId, error = getChainId(chain, ev.sourcePort, ev.sourceChannel, ev.Height)
            if error != nil { return (nil, error) }      
                        
            chain = GetChain(chainId)
            if chain == nil { return (nil, Error.DROP) }
                        
            return (chain, nil)   
        
        case WriteAcknowledgementEvent:
            chainId, error = getChainId(chain, ev.Port, ev.Channel, ev.Height)
            if error != nil { return (nil, error) }      
            
            chain = GetChain(chainId)
            if chain == nil { nil, Error.DROP }
            
            return (chain, nil)   
    }
}

// Return chaindId of the destination chain based on port and channel info for the given chain
func getChainId(chain Chain, port Identifier, channel Identifier, height Height) (String, Error) {
    channel, proof, error = GetChannel(chain, port, channel, height)
    if error != nil { return (nil, error) }
                                
    connectionId = channel.connectionHops[0]
    connection, proof, error = GetConnection(chain, connectionId, height) 
    if error != nil { return (nil, error) }
                                
    clientState, proof, error = GetClientState(chain, connection.clientIdentifier, height) 
    if error != nil { return (nil, error) }
    
    return (clientState.chainID, error) 
}

// Perform an update on `dest` chain for the IBC client for `src` chain.
//    Preconditions:
//      - `src` chain has height greater or equal to `targetHeight`
//    Postconditions:
//      - returns the installedHeight >= targetHeight
//      - return error if some of verification steps fail
func updateIBCClient(dest Chain, src Chain, targetHeight Height) -> (Height, Error) {
    
    clientState, proof, error = GetClientState(dest, dest.clientId, LATEST_HEIGHT)
    if error != nil { return (nil, error) } 
    // NOTE: What if a full node we are connected to send us stale (but correct) information regarding targetHeight?
    
    // if installed height is smaller than the targetHeight, we need to update client with targetHeight
    while (clientState.latestHeight < targetHeight) {
        // Do an update to IBC client for `src` on `dest`.
        shs, error = src.lc.getMinimalSet(clientState.latestHeight, targetHeight)
        if error != nil { return (nil, error) }    
    
        error = dest.submit(createUpdateClientDatagrams(shs))
        if error != nil { return (nil, error) } 
        
        clientState, proof, error = GetClientState(dest, dest.clientId, LATEST_HEIGHT)
        if error != nil { return (nil, error) }    
    }
    
    // NOTE: semantic check of the installed header is done using fork detection component
    return { clientState.Height, nil }        
}
```

  
     


 

