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

## Data Types

```go
type ClientState struct {
    Height          Height
    SignedHeader    SignedHeader	
}
```

```go
type MembershipProof struct {
    Height          Height
    Proof           Proof	
}
```

## Relayer algorithm

We assume the existence of the following helper functions:

```go
// returns ClientState for the targetHeight if it exists; otherwise returns ClientState at the latest height.
// We assume that this function handles non-responsive full node error by switching to a different full node.
queryClientConsensusState(chainA, targetHeight) (ClientState, MembershipProof)
verifyClientStateProof(clientStateAonB, membershipProof, sh.appHash) boolean
pendingDatagrams(height, chainA, chainB) IBCDatagram[]
verifyProof(datagrams, sh.appHash) boolean
createUpdateClientDatagrams(shs) IBCDatagram[]
submit(datagrams) error
replaceFullNode(chain)   
```

The main relayer event loop is a pipeline of three stages. Assuming some IBC event at height `h` on `chainA`, 
the relayer:

1. Updates (on `chainB`) the IBC client for `chainA` to a certain height `H` where `H >= h+1`.
2. Create IBC datagrams at height `H-1`.
3. Submit the datagrams from stage (2) to `chainB`.

Note that an IBC event at height `h` corresponds to the modifications to the data store made as part of executing
block at height `h`. The corresponding proof (that data is indeed written to the data store) can be verified using
the data store root hash that is part of the header at height `h+1`.

Once stage 1 finishes correctly, stage 2 should succeed assuming that `chainB` has not already processed the event. The 
interface between stage 1 and stage 2 is just the height `H`. Once stage 2 finishes correctly, stage 3 should 
succeed. The interface between stage 2 and stage 3 is a set of datagrams.

We assume that the corresponding light client is correctly installed on each chain. 

```golang
func handleEvent(ev, chainA) {
    // NOTE: we don't verify if event data are valid at this point. We trust full node we are connected to
    // until some verification fails. Otherwise, we can have Stage 2 (datagram creation being done first).
    
    // Stage 1.
    // Determine destination chain
    chainB = GetDestinationInfo(ev, chainA)   

    // Stage 2.
    // Update on `chainB` the IBC client for `chainA` to height `>= targetHeight`.
    targetHeight = ev.height + 1
    // See the code for `updateIBCClient` below.
    installedHeight, error := updateIBCClient(chainB, chainA, targetHeight)
    if error != nil {
       return error
    }

    // Stage 3.
    // Create the IBC datagrams including `ev` & verify them.
    datagram = createDatagram(ev, chainA, chainB, installedHeight)
    
    // Stage 4.
    // Submit datagrams.
    if datagram != nil {
        chainB.submit(datagram)
    }   
}


// Perform an update on `dest` chain for the IBC client for `src` chain.
//    Preconditions:
//      - `src` chain has height greater or equal to `targetHeight`
//    Postconditions:
//      - returns the installedHeight >= targetHeight
//      - return error if verification of client state fails
func updateIBCClient(dest, src, targetHeight) -> {installedHeight, error} {
    
    while (true) { 
        // Check if targetHeight exists already on destination chain.
        // Query state of IBC client for `src` on chain `dest`.
        clientState, membershipProof = dest.queryClientConsensusState(src, targetHeight)    
        // NOTE: What if a full node we are connected to send us stale (but correct) information regarding targetHeight?
        
        // Verify the result of the query
        sh = dest.lc.get_header(membershipProof.Height + 1)
        // NOTE: Headers we obtain from the light client are trusted. 
        if verifyClientStateProof(clientState, membershipProof, sh.appHash) {
            break;
        }
        replaceFullNode(dst)        
    }
    
    // At this point we know that clientState is indeed part of the state on dest chain.              
    // Verify if installed header is equal to the header obtained the from the local client 
    // at the same height.  
    if !src.lc.get_header(clientState.Height) == clientState.SignedHeader.Header {
        // We know at this point that conflicting header is installed at the dst chain.
        // We need to create proof of fork and submit it to src chain and to dst chain so light client is frozen.
        src.lc.createAndSubmitProofOfFork(dst, clientState)
        return {nil, error}
    }
               
    while (clientState.Height < targetHeight) {
        // Installed height is smaller than the target height.
        // Do an update to IBC client for `src` on `dest`.
        shs = src.lc.get_minimal_set(clientState.Height, targetHeight)
        // Blocking call. Wait until transaction is committed to the dest chain.
        dest.submit(createUpdateClientDatagrams(shs))
    
        while (true) { 
            // Check if targetHeight exists already on destination chain.
            // Query state of IBC client for `src` on chain `dest`.
            clientState, membershipProof = dest.queryClientConsensusState(src, targetHeight)    
            // NOTE: What if a full node we are connected to send us stale (but correct) information regarding targetHeight?
                
            // Verify the result of the query
            sh = dest.lc.get_header(membershipProof.Height + 1)
            // NOTE: Headers we obtain from the light client are trusted. 
            if verifyClientStateProof(clientState, membershipProof, sh.appHash) {
                break;
            }
            replaceFullNode(dst)        
        }
            
        // At this point we know that clientState is indeed part of the state on dest chain.              
        // Verify if installed header is equal to the header obtained the from the local client 
        // at the same height.  
        if !src.lc.get_header(clientState.Height) == clientState.SignedHeader.Header {
            // We know at this point that conflicting header is installed at the dst chain.
            // We need to create proof of fork and submit it to src chain and to dst chain so light client is frozen.
            src.lc.createAndSubmitProofOfFork(dst, clientState)
            return {nil, error}
        }
    }

    return {clientState.Height, nil}
}
```

## System model

We assume that a correct relayer operates in the following model:

### Connected chains

Relayer transfers data between two chains: chainA and chainB. For simplicity, we assume Tendermint chains. 
Each chain operates under Tendermint security model:
- given a block b at height h committed at time t = b.Header.Time, +2/3 of voting power behaves correctly
at least before t + UNBONDING_PERIOD, where UNBONDING_PERIOD is a system parameter (typically order of weeks).
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
`verifyMembership(header.AppHash, h, proof, path, d)` that returns `true` if data was committed by the corresponding
chain at height *h*. The trusted header is provided by the corresponding light client. 
  

  
     


 

- it transfers data between two chains: chainA and chainB. This implies that a 
relayer has connections with full nodes from chainA and chainB in order to inspect their
state. We assume that blockchain applications that operates on top of chainA and chainB writes
relevant data into publicly available data store (for example IBC packets). 
- in order to verify data written by the application to its store, a relayer needs
light client node for each connected chain. Light client will on its own establish connections
with multiple 
