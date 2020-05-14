---------------------------- MODULE Environment ----------------------------

(***************************************************************************

    This module is part of the TLA+ specification for the
    IBC Connection Handshake (CH) protocol. This is a high-level spec of CH.
    
    This module captures the operators and actions outside of the CH protocol
    itself (i.e., the environment).
    Among others, the environment does the following:
    - creates two instances of ConnectionHandshakeModule,
    - wires these instances together,
    - simulates some malicious behavior by injecting incorrect messages
    - provides the initialization step for CH protocol, concretely a
    "CHMsgInit" message, so that the two instances can perform the protocol.
    - updates the clients on each instance periodically, or advances the chain
    of each instance. 

  ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences


CONSTANT MaxHeight,     \* Maximum height of any chain in the system.
         MaxBufLen      \* Length (size) of message buffers.

ASSUME MaxHeight > 1
ASSUME MaxBufLen > 1


VARIABLES
    bufChainA,      \* A buffer (sequence) for messages inbound to chain A.
    bufChainB,      \* A buffer for messages inbound to chain B.
    storeChainA,    \* The local store of chain A.
    storeChainB,    \* The local store of chain B.
    maliciousEnv    \* If TRUE, environment interferes w/ CH protocol. 


chainAParameters == [
    connectionIDs |-> { "connAtoB" },
    clientIDs |-> { "clientIDChainA" }
]

chainBParameters == [
    connectionIDs |-> { "connBtoA" },
    clientIDs |-> { "clientIDChainB" }
]


ClientIDs == { chainAParameters.clientIDs, chainBParameters.clientIDs }
ConnectionIDs == { chainAParameters.connectionIDs, chainBParameters.connectionIDs }


(* Bundle with variables that chain A has access to. *)
chainAVars == <<bufChainA,      (* Input message buffer. *)
                bufChainB,      (* Output message buffer. *)
                storeChainA>>   (* The local chain store. *)

(* Bundle with variables that chain B has access to. *)
chainBVars == <<bufChainB,      (* Input message buffer. *)
                bufChainA,      (* Output message buffer. *)
                storeChainB>>   (* Local chain store. *)

(* All variables specific to chains. *)
chainStoreVars == <<storeChainA, storeChainB>>

allVars == <<chainStoreVars, bufChainA, bufChainB, maliciousEnv>>

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inBuf          <- bufChainA,
             outBuf         <- bufChainB,
             store          <- storeChainA,
             ConnectionIDs  <- chainAParameters.connectionIDs,
             ClientIDs      <- chainAParameters.clientIDs


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inBuf          <- bufChainB,      (* Flip the message buffers w.r.t. chain A buffers. *)
             outBuf         <- bufChainA,      (* Inbound for "A" is outbound for "B". *)
             store          <- storeChainB,
             ConnectionIDs  <- chainBParameters.connectionIDs,
             ClientIDs      <- chainBParameters.clientIDs


(* TODO BLOCK COMMENTS *)
ConnectionParameters ==
    [
        localEnd : chmA!ConnectionEnds,
        remoteEnd : chmB!ConnectionEnds
    ]


(******************************* Connections *******************************
     A set of connection end records.
     A connection end record contains the following fields:

     - connectionID -- a string 
       Stores the identifier of this connection, specific to a chain.

     - clientID -- a string
       Stores the identifier of the client running on this chain.  
     
 ***************************************************************************)
Connections ==
    [
        parameters : ConnectionParameters,
        state : ConnectionStates
    ]


(******************************* ConnProof *********************************
     A set of records describing the possible values for connection proofs.
     
     A connection proof record contains the following fields:

     - connectionState -- a string 
       Captures the state of the connection in the local store of the module
       which created this proof.

     - height -- a Nat
       The current height (latestHeight) of the chain at the moment when the
       module created this proof.

 ***************************************************************************)
ConnProofs ==
    [
        connectionState : ConnectionStates, 
        height : 1..MaxHeight
    ]


(******************************* ClientProofs *******************************
     A set of records describing the possible values for client proofs.
     
     A client proof record contains the following fields:

     - height -- a Nat
       The current height (latestHeight) of the client colocated with module
       which created this proof.

 ***************************************************************************)
ClientProofs ==
    [
        height : 1..MaxHeight
    ]


Heights == 1..MaxHeight


(******************************** Messages ********************************
Messages are connection handshake specific.
 
    The valid message types are defined in:
    ConnectionHandshakeModule.CHMessageTypes.
    
In the low-level connection handshake protocol, the four messages have the
following types: ConnOpenInit, ConnOpenTry, ConnOpenAck, ConnOpenConfirm.
 These are described in ICS 003.
 In this high-level specification, we choose slightly different names, to
 make an explicit distinction to the low-level protocol. Message types
 are as follows: CHMsgInit, CHMsgTry, CHMsgAck, and CHMsgConfirm. Notice that
 the fields of each message are also different to the ICS 003 specification.
 
 
 ***************************************************************************)
ConnectionHandshakeMessages ==
    [type : {"CHMsgInit"}, 
     parameters : ConnectionParameters]
    \union
    [type : {"CHMsgTry"},
     parameters : ConnectionParameters,
     connProof : ConnProofs,
     clientProof : ClientProofs]
    \union
    [type : {"CHMsgAck"},
     parameters : ConnectionParameters,
     connProof : ConnProofs,
     clientProof : ClientProofs]
     \union
    [type : {"CHMsgConfirm"},
     parameters : ConnectionParameters,
     connProof : ConnProofs]


(* The set of all Init messages, such that the local end is the
    set 'le', and the remote end is set 're'. *)
InitMsgs(le, re) ==
    [type : {"CHMsgInit"},
     parameters : [localEnd : le,
                   remoteEnd : re]]


(***************************************************************************
 Environment actions.
 ***************************************************************************)


(* Assigns a sequence with 1 element -- the Init msg -- to either bufChainA
    or bufChainB. *)
InitEnv ==
    /\ maliciousEnv = TRUE
    /\ \/ /\ bufChainA \in {<<msg>> : 
                msg \in InitMsgs(chmA!ConnectionEnds, chmB!ConnectionEnds)}
          /\ bufChainB = <<>>   (* Empty buffer initially. *)
       \/ /\ bufChainB \in {<<msg>> :
                msg \in InitMsgs(chmB!ConnectionEnds, chmA!ConnectionEnds)}
          /\ bufChainA = <<>>


(* May change either of the store of chain A or B. 
 *)
GoodNextEnv ==
    \/ /\ chmA!NotMaxHeight
       /\ \/ chmA!AdvanceChainHeight 
          \/ chmA!UpdateClient(storeChainB.latestHeight)
       /\ UNCHANGED storeChainB
    \/ /\ chmB!NotMaxHeight
       /\ \/ chmB!AdvanceChainHeight
          \/ chmB!UpdateClient(storeChainA.latestHeight)
       /\ UNCHANGED storeChainA


(* The environment injects a msg. in the buffer of one of the chains. 
   This interferes with the CH protocol in two ways:
    1. by introducing additional messages that are incorrect,
    2. by dropping correct messages (overwritting them).
    
    Without the first constraint, on the "Len(bufChainA)" and "Len(bufChainB)",
    Env could fill buffers (DoS attack). This can lead to a deadlock, because
    chains will simply be unable to reply to each other.
 *)
MaliciousNextEnv ==
    \/ /\ Len(bufChainA) < MaxBufLen - 1
       /\ bufChainA' \in {Append(bufChainA, arbitraryMsg) : 
            arbitraryMsg \in ConnectionHandshakeMessages}
       /\ UNCHANGED bufChainB
    \/ /\ Len(bufChainB) < MaxBufLen - 1
       /\ bufChainB' \in {Append(bufChainB, arbitraryMsg) :
            arbitraryMsg \in ConnectionHandshakeMessages}
       /\ UNCHANGED bufChainA


NextEnv ==
    \/ /\ GoodNextEnv
       /\ UNCHANGED<<bufChainA, bufChainB, maliciousEnv>>
    \/ /\ maliciousEnv = TRUE
       /\ MaliciousNextEnv
       /\ UNCHANGED<<maliciousEnv, chainStoreVars>>
    \/ /\ maliciousEnv = TRUE
       /\ maliciousEnv' = FALSE
       /\ UNCHANGED<<bufChainA, bufChainB, chainStoreVars>>


CHProtocolDone ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED <<allVars>>


(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID as well as a client.
 *)
Init ==
    /\ \E clientB \in chmB!InitClients : chmA!Init("chainA", clientB)
    /\ \E clientA \in chmA!InitClients : chmB!Init("chainB", clientA)
    /\ InitEnv


\* The two CH modules and the environment alternate their steps.
Next ==
    \/ CHProtocolDone
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED <<storeChainB, maliciousEnv>>
    \/ chmB!Next /\ UNCHANGED <<storeChainA, maliciousEnv>>


FairProgress ==
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)
    /\ WF_chainStoreVars(GoodNextEnv)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


(* TODO: Unclear how to capture the type of a sequence. *)
TypeInvariant ==
    /\ \/ bufChainA \in Seq(ConnectionHandshakeMessages)
       \/ bufChainB \in Seq(ConnectionHandshakeMessages)


\* Liveness property.
Termination ==
    <> ~ maliciousEnv
        => <> /\ storeChainA.connection.state = "OPEN"
              /\ storeChainB.connection.state = "OPEN"


\* Safety property.
\* If the connections in the two chains are not null, then the
\* connection parameters must always match.
ConsistencyInv ==
    \/ storeChainA.connection = chmA!nullConnection
    \/ storeChainB.connection = chmB!nullConnection
    \/ storeChainA.connection.parameters 
        = chmB!FlipConnectionParameters(storeChainB.connection.parameters)

Consistency ==
    [] ConsistencyInv

=============================================================================
\* Modification History
\* Last modified Thu May 14 16:36:27 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

