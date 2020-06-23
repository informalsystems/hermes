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
queryClientConsensusState(chainA, datagramProofHeight) (ClientState, MembershipProof)
verifyClientStateProof(clientStateAonB, membershipProof, sh.appHash) boolean
pendingDatagrams(height, chainA, chainB) IBCDatagram[]
verifyProof(datagrams, sh.appHash) boolean
```

The pseudocode of the main relayer event loop is the following: 

```go
func handleEvent(ev, chainA, chainB) {
    datagramsProofHeight = ev.height + 1
    
    // query client state of chain A on chain B for proof height
    clientStateAonB, membershipProof = chainB.queryClientConsensusState(chainA, datagramProofHeight)
      
    // verify client state
    sh = chainB.lc.getHeader(membershipProof.Height + 1)
    if !verifyClientStateProof(clientStateAonB, membershipProof, sh.appHash) then return error
      
    while datagramsProofHeight > clientStateAonB.Height {
        // we need to update client for A on B before submitting datagram
        shs = chainA.lc.get_minimal_set(clientStateAonB.Height, datagramsProofHeight)
        chainB.submit(createUpdateClientDatagrams(shs)) // might fail to be processed because of conncurent client update
                
        // query client state of chain A on chain B for proof height
        clientStateAonB, membershipProof = chainB.queryClientConsensusState(chainA, datagramProofHeight)
                      
        // verify client state
        sh = chainB.lc.getHeader(membershipProof.Height + 1)
        if !verifyClientStateProof(clientStateAonB, membershipProof, sh.appHash) then return error
    }

    if datagramsProofHeight < clientStateAonB.Height {
        handleEvent(IBCEvent(clientStateAonB.Height - 1), chainA, chainB)
    } 
    
    // datagramsProofHeight is installed on chain B so we can submit datagrams
    
    // create the corresponding IBC datagram
    datagrams = pendingDatagrams(ev.Height, chainA, chainB)
   
    // verify datagrams
    sh = chainA.lc.getHeader(datagramsProofHeight)
    if !verifyProof(datagrams, sh.appHash) then return error
    
    // submit datagrams
    chainB.submit(datagrams)  
}
```  