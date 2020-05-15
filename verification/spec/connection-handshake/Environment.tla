---------------------------- MODULE Environment ----------------------------

(***************************************************************************

    This module is part of the TLA+ specification for the IBC Connection
    Handshake protocol (identifier 'ICS3'). This is a high-level spec of ICS3.
    
    This module captures the operators and actions outside of the CH protocol
    itself (i.e., the environment).
    Among others, the environment does the following:
    - creates two instances of ConnectionHandshakeModule,
    - wires these instances together,
    - simulates some malicious behavior by injecting incorrect messages
    - provides the initialization step for ICS3 protocol, concretely a
    "ICS3MsgInit" message, so that the two instances can perform the protocol.
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
    clientIDs |-> { "clientIDChainB" }
]

chainBParameters == [
    connectionIDs |-> { "connBtoA" },
    clientIDs |-> { "clientIDChainA" }
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
             inBuf          <- bufChainB,      (* Flip message buffers *)
             outBuf         <- bufChainA,      (* Inbound of "A" is outbound of "B". *)
             store          <- storeChainB,
             ConnectionIDs  <- chainBParameters.connectionIDs,
             ClientIDs      <- chainBParameters.clientIDs


(******************************* ConnectionParameters **********************
     A set of connection parameter records.
     A connection parameter record contains the following fields:

     - localEnd -- a connection end 
       Specifies the local connection details (i.e., connection ID and
       client ID).

     - remoteEnd -- a connection end
       Specifies the local connection details.  

 ***************************************************************************)
ConnectionParameters ==
    [
        localEnd : chmA!ConnectionEnds,
        remoteEnd : chmB!ConnectionEnds
    ]


(******************************* Connections *******************************
     A set of connection records.
     A connection record contains the following fields:

     - parameters -- a connection parameters record 
       Specifies the local plus remote ends.

     - state -- a connection state (see ConnectionStates set).
     
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


(******************************* ICS3MessageTypes *****************************

    The set of valid message types that the ConnectionHandshakeModule can 
    handle, e.g., as incoming or outgoing messages.

    In the low-level connection handshake protocol, the four messages have
    types: ConnOpenInit, ConnOpenTry, ConnOpenAck, ConnOpenConfirm.
    In this high-level specification, we choose slightly different names, to
    make an explicit distinction to the low-level protocol. Message types
    are as follows:
    ICS3MsgInit, ICS3MsgTry, ICS3MsgAck, and ICS3MsgConfirm.
    For a complete description of the message record, see
    ConnectionHandshakeMessage below.
     
 ***************************************************************************)
ICS3MessageTypes ==
    {"ICS3MsgInit", 
     "ICS3MsgTry",
     "ICS3MsgAck",
     "ICS3MsgConfirm"}


(*********************** ConnectionHandshakeMessages ***********************

    The set of ConnectionHandshakeMessage records.
    These are connection handshake specific messages that two chains exchange
    while executing the ICS3 protocol.
 
 ***************************************************************************)
ConnectionHandshakeMessages ==
    [type : {"ICS3MsgInit"}, 
     parameters : ConnectionParameters]
    \union
    [type : {"ICS3MsgTry"},
     parameters : ConnectionParameters,
     connProof : ConnProofs,
     clientProof : ClientProofs]
    \union
    [type : {"ICS3MsgAck"},
     parameters : ConnectionParameters,
     connProof : ConnProofs,
     clientProof : ClientProofs]
     \union
    [type : {"ICS3MsgConfirm"},
     parameters : ConnectionParameters,
     connProof : ConnProofs]




(***************************** InitMsgs ***********************************

    The set of ConnectionHandshakeMessage records where message type is
    ICS3MsgInit.

    This operator returns the set of all initialization messages, such that
    the local end is the set 'le', and the remote end is set 're'.
 
 ***************************************************************************)
InitMsgs(le, re) ==
    [type : {"ICS3MsgInit"},
     parameters : [localEnd : le,
                   remoteEnd : re]]


(***************************************************************************
 Environment actions.
 ***************************************************************************)


(* Assigns a sequence with 1 element -- the Init msg -- to either bufChainA
    or bufChainB. 
    
    TODO: Maybe reduce this. 
 *)
InitEnv ==
    /\ maliciousEnv = TRUE
    /\ bufChainA \in {<<msg>> :
            msg \in InitMsgs(chmA!ConnectionEnds, chmB!ConnectionEnds)}
    /\ bufChainB \in {<<msg>> :
            msg \in InitMsgs(chmB!ConnectionEnds, chmA!ConnectionEnds)}


(* May change either of the store of chain A or B. 
 *)
GoodNextEnv ==
    \/ /\ chmA!CanProgress
       /\ \/ chmA!AdvanceChainHeight
          \/ chmA!UpdateClient(storeChainB.latestHeight)
       /\ UNCHANGED storeChainB
    \/ /\ chmB!CanProgress
       /\ \/ chmB!AdvanceChainHeight
          \/ chmB!UpdateClient(storeChainA.latestHeight)
       /\ UNCHANGED storeChainA


(* The environment injects a msg. in the buffer of one of the chains. 
    This interferes with the ICS3 protocol by introducing additional
    messages that are usually incorrect.
    
    Without the first constraint, on the "Len(bufChainA)" and
    "Len(bufChainB)", Env could fill buffers (DoS attack). This can
    lead to a deadlock, because chains will simply be unable to reply
    to each other.
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


ICS3ProtocolDone ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED <<allVars>>


(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID and a client. *)
Init ==
    /\ \E clientA \in chmA!InitClients : chmA!Init("chainA", clientA)
    /\ \E clientB \in chmB!InitClients : chmB!Init("chainB", clientB)
    /\ InitEnv


(* The two ICS3 modules and the environment alternate their steps. *)
Next ==
    \/ ICS3ProtocolDone
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED <<storeChainB, maliciousEnv>>
    \/ chmB!Next /\ UNCHANGED <<storeChainA, maliciousEnv>>


FairProgress ==
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)
\*    /\ WF_chainStoreVars(GoodNextEnv)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


TypeInvariant ==
    /\ \/ bufChainA \in Seq(ConnectionHandshakeMessages)
       \/ bufChainB \in Seq(ConnectionHandshakeMessages)


(* Liveness property. *)
(* As long as all chains CanProgress: We should reach open & open. *)
Termination ==
    <> [](chmA!CanProgress /\ chmB!CanProgress) 
        => [](/\ storeChainA.connection.state = "OPEN"
              /\ storeChainB.connection.state = "OPEN")


(* Safety property. *)
ConsistencyProperty ==
    \/ storeChainA.connection.state = "OPEN"
    \/ storeChainB.connection.state = "OPEN"
    (* If the connections in the two chains are not null, then the
        connection parameters must always match.
     *)
    => storeChainA.connection.parameters 
        = chmB!FlipConnectionParameters(storeChainB.connection.parameters)

Consistency ==
    [] ConsistencyProperty

=============================================================================
\* Modification History
\* Last modified Fri May 15 13:01:37 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

