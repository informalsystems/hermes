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

### Data Types

```go
type ClientState struct {
    Height          Height
    Header          SignedHeader	
}
```

```go
type MembershipProof struct {
    Height          Height
    Proof           Proof	
}
```

### Relayer algorithm

We assume the existence of the following helper functions:

```go
// returns ClientState for the targetHeight if it exists; otherwise returns ClientState at the latest height
queryClientConsensusState(chainA, targetHeight) (ClientState, MembershipProof)
verifyClientStateProof(clientStateAonB, membershipProof, sh.appHash) boolean
pendingDatagrams(height, chainA, chainB) IBCDatagram[]
verifyProof(datagrams, sh.appHash) boolean
createUpdateClientDatagrams(shs) IBCDatagram[]
submit(datagrams) error
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

```golang
func handleEvent(ev, chainA, chainB) {
    // NOTE: we don't verify if event data are valid at this point. We trust full node we are connected to
    // until some verification fails. 
   
    // Stage 1.
    // Update on `chainB` the IBC client for `chainA` to height `>= targetHeight`.
    targetHeight = ev.height + 1
    // See the code for `updateIBCClient` below.
    installedHeight, error := updateIBCClient(chainB, chainA, targetHeight)
    if error != nil {
        // Updating the IBC client failed because of verification error.
        // TODO: Add fork detection logic
        // Connect to a different full node of `chainB` and retry.
    }

    // Stage 2.
    // Create the IBC datagrams including `ev` & verify them.
    datagrams = pendingDatagrams(installedHeight - 1, chainA, chainB)
    sh = chainA.lc.get_header(installedHeight)
    if !verifyProof(datagrams, sh.appHash) {
        return error;  // Full node for `chainA` is faulty. Connect to different node of `chainA` and retry.
    }
    // Stage 3.
    // Submit datagrams.
    err = chainB.submit(datagrams)
    if err != nil {
        return error;  // Full node for `chainB` is faulty. Connect to different node of `chainB` and retry.
    }
}


// Perform an update on `dest` chain for the IBC client for `src` chain.
//    Preconditions:
//      - `src` chain has height greater or equal to `targetHeight`
//    Postconditions:
//      - returns the installedHeight >= targetHeight
//      - return error if verification of client state fails
func updateIBCClient(dest, src, targetHeight) -> {installedHeight, error} {
    
    // Check if targetHeight exists already on destination chain.
    // Query state of IBC client for `src` on chain `dest`.
    clientState, membershipProof = dest.queryClientConsensusState(src, targetHeight)    
            
    // Verify if installed header is equal to the header obtained the from the local client 
    // at the same height
    if !src.lc.get_header(clientState.Height) == clientState.SignedHeader.Header {
        return {nil, error}
    }
            
    // Verify the result of the query
    sh = dest.lc.get_header(membershipProof.Height + 1)
    if !verifyClientStateProof(clientState, membershipProof, sh.appHash) then return {nil, error}
    
    while (clientState.Height < targetHeight) {
        // Installed height is smaller than the target height.
        // Do an update to IBC client for `src` on `dest`.
        shs = src.lc.get_minimal_set(clientState.Height, targetHeight)
        // Might fail due to conncurent client updates.
        dest.submit(createUpdateClientDatagrams(shs))

        // Check if targetHeight exists already on destination chain.
        // Query state of IBC client for `src` on chain `dest`.
        clientState, membershipProof = dest.queryClientConsensusState(src, targetHeight)
            
        // Verify if installed header is equal to the header obtained the from the local client 
        // at the same height
        if !src.lc.get_header(clientState.Height) == clientState.SignedHeader.Header {
            return {nil, error}
        }
                    
        // Verify the result of the query
        sh = dest.lc.get_header(membershipProof.Height + 1)
        if !verifyClientStateProof(clientState, membershipProof, sh.appHash) then return {nil, error}
    }

    return {clientState.Height, nil}
}
```

