---------------------------- MODULE Environment ----------------------------

(***************************************************************************

    This module is part of the TLA+ specification for the IBC Connection
    Handshake protocol (identifier 'ICS3'). This is a high-level spec of ICS3.
    
    This module captures the operators and actions outside of the ICS3 protocol
    itself (i.e., the environment).
    Among others, the environment does the following:
    - creates two instances of ICS3Module;
    - wires these instances together;
    - provides the initialization step for ICS3 protocol, concretely a
    "ICS3MsgInit" message, so that the two instances can perform the protocol;
    - some relayer functionality: passes any outgoing message from a chain
    into the ingoing buffer of the other (destination) chain and correspondingly
    updates the client of the destination chain;
    - also, advances the chain of each instance non-deterministically;
    - if `Concurrency` is TRUE, then this module can take non-deterministic
    steps, by updating the client on a chain.

 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, ICS3Utils


CONSTANT MaxHeight,      \* Maximum height of any chain in the system.
         MaxBufLen,      \* Length (size) of message buffers.
         Concurrency,    \* Flag for enabling concurrent relayers.
         MaxVersionNr,   \* Maximum version number.
         VersionPickMode \* The mode for picking versions.


ASSUME MaxHeight > 4
ASSUME MaxBufLen >= 1
ASSUME VersionPickMode \in {"overwrite", "onTryDet", "onTryNonDet", "onAckDet", "onAckNonDet"}

(*
VersionPickMode: 
    * "overwrite" -- the version is picked deterministically when handling 
                 ICS3MsgTry from the intersection of versions sent in the 
                 message and locally supported versions. The picked version 
                 is sent to the counterparty chain in ICS3MsgAck, which overwrites its
                 own version with the one from the message
    * "onTryDet" -- the version is picked deterministically when handling 
                 ICS3MsgTry from the intersection of versions sent in the 
                 message and locally supported versions. The picked version 
                 is sent to the counterparty chain in ICS3MsgAck, which accepts it
    * "onTryNonDet" -- same as "onTryDet", except the version is picked 
                 non-deterministically
    * "onAckDet" -- the version is picked deterministically when handling  
                 ICS3MsgAck from the intersection of versions sent in the 
                 message and locally supported versions. The picked version 
                 is sent to the counterparty chain in ICS3MsgConfirm, which accepts it
    * "onAckNonDet" -- same as "onAckDet", except the version is picked 
                 non-deterministically              
*)

VARIABLES
    inBufChainA,    \* A buffer (sequence) for messages inbound to chain A.
    inBufChainB,    \* A buffer for messages inbound to chain B.
    outBufChainA,   \* A buffer for messages outgoing from chain A.
    outBufChainB,   \* A buffer for messages outgoing from chain B.
    storeChainA,    \* The local store of chain A.
    storeChainB     \* The local store of chain B.

(************* ChainAConnectionEnds & ChainBConnectionEnds *****************

    The set of records that each chain can use as a valid local connection
    end. For each chain, this set contains one record, since we are
    modeling a single connection in this specification.
 
 ***************************************************************************)

AllChainIDs ==
    { "chainA", "chainB" }
    
AllVersionSeqs ==
    {<<>>} \union
    {<<a>> : a \in 1..MaxVersionNr} \union
    {<<a, b>> \in (1..MaxVersionNr) \X (1..MaxVersionNr) : a /= b}   
    
ChainAConnectionEnds == 
    [
        connectionID : { "connAtoB" },
        clientID : { "clientOnAToB" }
    ]
ChainBConnectionEnds ==
    [
        connectionID : { "connBtoA" },
        clientID : { "clientOnBToA" }
    ]

AllConnectionEnds ==
    ChainAConnectionEnds \union ChainBConnectionEnds    
    
AllClientIDs == 
    { x.clientID : x \in AllConnectionEnds }

AllConnectionIDs ==
    { x.connectionID : x \in AllConnectionEnds }    

ChainAClientIDs ==
    { x.clientID : x \in ChainAConnectionEnds }

ChainBClientIDs ==
    { x.clientID : x \in ChainBConnectionEnds }

ChainAConnectionIDs ==
    { x.connectionID : x \in ChainAConnectionEnds }

ChainBConnectionIDs ==
    { x.connectionID : x \in ChainBConnectionEnds }

(* Bundle with variables that chain A has access to. *)
chainAVars == <<inBufChainA,    (* Input message buffer. *)
                outBufChainA,   (* Output message buffer. *)
                storeChainA>>   (* The local chain store. *)

(* Bundle with variables that chain B has access to. *)
chainBVars == <<inBufChainB,    (* Input message buffer. *)
                outBufChainB,   (* Output message buffer. *)
                storeChainB>>   (* Local chain store. *)

(* All variables specific to both chains. *)
chainStoreVars == <<storeChainA, storeChainB>>

allVars == <<chainStoreVars, 
             inBufChainA, inBufChainB, 
             outBufChainA, outBufChainB>>


(* This is a separate module comprising common type definitions. *)
INSTANCE ICS3Types

chmA == INSTANCE ICS3Module
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- inBufChainA,
             outBuf         <- outBufChainA,
             store          <- storeChainA,
             ConnectionIDs  <- ChainAConnectionIDs,
             ClientIDs      <- ChainAClientIDs,
             ChainID        <- "chainA"


chmB == INSTANCE ICS3Module
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- inBufChainB,
             outBuf         <- outBufChainB,
             store          <- storeChainB,
             ConnectionIDs  <- ChainBConnectionIDs,
             ClientIDs      <- ChainBClientIDs,
             ChainID        <- "chainB"


(***************************************************************************
 Environment actions.
 ***************************************************************************)


(* Environment initialization.

    This action kick-starts the ICS3 protocol by assigning an ICS3MsgInit
    msg to either of the two chains (or both).

 *)
InitEnv ==            
    /\ \/ /\ inBufChainA \in {<<msg>> : (* ICS3MsgInit to chain A. *)
                        msg \in InitMsgs(ChainAConnectionEnds, ChainBConnectionEnds)}
          /\ inBufChainB = <<>>
       \/ /\ inBufChainB \in {<<msg>> : (* ICS3MsgInit to chain B. *)
                        msg \in InitMsgs(ChainBConnectionEnds, ChainAConnectionEnds)} 
          /\ inBufChainA = <<>>
       \/ /\ inBufChainA \in {<<msg>> : (* ICS3MsgInit to both chains. *)
                        msg \in InitMsgs(ChainAConnectionEnds, ChainBConnectionEnds)} 
          /\ inBufChainB \in {<<msg>> :
                        msg \in InitMsgs(ChainBConnectionEnds, ChainAConnectionEnds)} 
    /\ outBufChainA = <<>>  (* Output buffers should be empty initially. *)
    /\ outBufChainB = <<>>


(* Message relaying functionality of the environment.

    This is part of the RelayNextEnv sub-action of the environment.
    This performs a basic relaying step, that is, passing a message from the
    output buffer of one of the chains (paramter 'from') into the input buffer
    of another chain (parameter 'to').

 *)
RelayMessage(from, to) ==
    /\ from # <<>>
    /\ Len(to) < MaxBufLen - 1
    /\ to' = Append(to, Head(from))
    /\ from' = Tail(from)


(* Default next step for environment.

    This step may change (non-deterministically) either of the store of chain A
    or B, by advancing the height of that chain. This can only enable if the
    respective chain has ample steps left, i.e., the chain height is not within 4 steps
    of the maximum height. This precondition disallow continuos advancing of chain heights,
    and therefore allows chains to take meaningful steps (executing the ICS3 protocol to
    completion).

 *)
DefaultNextEnv ==
    \/ /\ MaxHeight - storeChainA.latestHeight > 4
       /\ chmA!AdvanceChainHeight
       /\ UNCHANGED<<storeChainB, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>
    \/ /\ MaxHeight - storeChainB.latestHeight > 4
       /\ chmB!AdvanceChainHeight
       /\ UNCHANGED<<storeChainA, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>


(* A concurrent UpdateClient step for the environment.

    This updates the client on one of the chains with the latest height of the other chain.
    This step helps to simulate the conditions of having multiple relayers acting in parallel.

*)
ConcurrentUpdateClient ==
       \/ /\ chmB!CanUpdateClient(storeChainA.latestHeight)
          /\ chmB!UpdateClient(storeChainA.latestHeight)
          /\ UNCHANGED<<storeChainA, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>
       \/ /\ chmA!CanUpdateClient(storeChainB.latestHeight)
          /\ chmA!UpdateClient(storeChainB.latestHeight)
          /\ UNCHANGED<<storeChainB, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>


(* Relaying step for the environment.

    This step performs a relay: moving a message between the output
    buffer of a chain to the input buffer of the other chain, and updating accordingly
    the client on the latter chain. 

 *)
RelayNextEnv ==
    (* Relay direction: from chain A to chain B. *)
    \/ LET msg == Head(outBufChainA)
           targetHeight == IF MessageTypeIncludesConnProof(msg.type)
                           THEN msg.proofHeight
                           ELSE storeChainA.latestHeight
       IN /\ RelayMessage(outBufChainA, inBufChainB)
          /\ \/ chmB!CanUpdateClient(targetHeight) 
                    /\ chmB!UpdateClient(targetHeight)
             \/ ~ chmB!CanUpdateClient(targetHeight)
                    /\ UNCHANGED storeChainB
          /\ UNCHANGED<<storeChainA, outBufChainB, inBufChainA>>
    (* Relay direction: from chain B to chain A. *)
    \/ LET msg == Head(outBufChainB)
           targetHeight == IF MessageTypeIncludesConnProof(msg.type)
                           THEN msg.proofHeight
                           ELSE storeChainB.latestHeight
       IN /\ RelayMessage(outBufChainB, inBufChainA)
          /\ \/ chmA!CanUpdateClient(targetHeight)
                    /\ chmA!UpdateClient(targetHeight)
             \/ ~ chmA!CanUpdateClient(targetHeight)
                    /\ UNCHANGED storeChainA
          /\ UNCHANGED<<storeChainB, outBufChainA, inBufChainB>>


(* Environment next action.

    There are three possible actions that the environment may perform:

    1. If `Concurrency` flag is TRUE, then the environment may update the
    client on one of the two chains. This effectively models what happens
    when more than a relayer triggers the `UpdateClient` action of a chain,
    a condition that can lead to liveness (termination) problems in ICS3. 
    
    2. A 'DefaultNextEnv' step, that simply advances the height of one of
    the chains unless the chain has just a few (namely, `4`) heights left.

    3. The environment may perform a relaying step, that is:
    if there is a message in the ougoing buffer of a chain, the relayer
    moves this message to the ingoing buffer of the other chain, and also
    updates the client on the latter chain.

 *)
NextEnv ==
    \/ Concurrency /\ ConcurrentUpdateClient
    \/ DefaultNextEnv
    \/ RelayNextEnv
    \/ UNCHANGED allVars


(* Enables when the connection is open on both chains.

    State predicate signaling that the protocol terminated correctly.

 *)
ICS3ReachedOpenConnection ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED allVars


(* Enables when both chains are stuck, i.e., unable to progress while
    their connection is not opened.

    State predicate signaling that the protocol terminated unsucessfully.

 *)
ICS3ImpossibleToAdvance ==
    /\ \/ (~ chmA!CanAdvance /\ storeChainA.connection.state # "OPEN")
       \/ (~ chmB!CanAdvance /\ storeChainB.connection.state # "OPEN")
    /\ UNCHANGED allVars


(******************************************************************************

    Main spec. The system comprises the environment plus the two instances of
    ICS3 modules.

 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID and a client.
    The ChainVersionsOverlap predicate is a necessary assumption for termination. 
 *)
Init ==
    /\ chmA!Init 
    /\ chmB!Init
    /\ ChainVersionsOverlap(storeChainA, storeChainB)
    /\ InitEnv


(* The two ICS3 modules and the environment alternate their steps
    non-deterministically. Eventually, the execution ends with either
    successful (ICS3ReachedOpenConnection sub-action) or unsuccesfull
    (ICS3ImpossibleToAdvance sub-action) termination.
*)
Next ==
    \/ ICS3ReachedOpenConnection
    \/ ICS3ImpossibleToAdvance
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED chainBVars
    \/ chmB!Next /\ UNCHANGED chainAVars


FairProgress ==
    /\ chmA!Fairness
    /\ chmB!Fairness
    /\ WF_<<chainAVars, chainBVars>>(RelayNextEnv)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


TypeInvariant ==
    /\ chmA!TypeInvariant
    /\ chmB!TypeInvariant


(* Liveness property.

    We expect to eventually always reach an OPEN connection on both chains.

    Naturally, this property may not hold if the two chains do not have
    sufficient number of heights they can advance to. In other words, the
    `MaxHeight` constant should be at least `4` for this property to hold.

    The `Concurrency` constant may also affect liveness.
*)
Termination ==
       <> [](/\ \/ storeChainA.connection.state = "OPEN"
                \/ storeChainA.latestHeight = MaxHeight
             /\ \/ storeChainB.connection.state = "OPEN"
                \/ storeChainB.latestHeight = MaxHeight)

(* Safety property.

    If the connections in the two chains are not null, then the
        connection parameters must always match.
 *)
ConsistencyProperty ==
    /\ storeChainA.connection.state # "UNINIT"
    /\ storeChainB.connection.state # "UNINIT"
    => storeChainA.connection.parameters 
        = chmB!FlipConnectionParameters(storeChainB.connection.parameters)


Consistency ==
    [] ConsistencyProperty

(* Complementary to the safety property above.

    If the connections in the two chains are both OPEN, then the
        connection version must be identical.
 *)
VersionInvariant ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"   
    => /\ Len(storeChainA.connection.version) = 1
       /\ Len(storeChainB.connection.version) = 1
       /\ storeChainA.connection.version = storeChainB.connection.version

=============================================================================
\* Modification History
\* Last modified Fri Aug 28 09:11:35 CEST 2020 by adi
\* Last modified Tue Aug 25 17:48:37 CEST 2020 by ilinastoilkovska
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi