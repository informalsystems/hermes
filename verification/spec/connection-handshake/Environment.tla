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
        localEnd : chmA!ConnectionEnds \union chmB!ConnectionEnds,
        remoteEnd : chmB!ConnectionEnds \union chmA!ConnectionEnds
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


(* Environment initialization.
    
    This action kick-stars the ICS3 protocol by assigning an ICS3MsgInit
    msg to either of the two chains (or both).
    
    Initially, the environment is non-malicious. The environment starts
    acting maliciously once the connection on both chains transitions out
    of state "UNINIT" (the initials state). It is important to
    initialize the protocol like this, otherwise the env. can provoke a
    deadlock. This can happen with the following sequence of actions:
    
    1. Environment injects a ICS3MsgInit to chain A with the following
    correct parameters:

        localEnd |-> [connectionID |-> "connAtoB",
                      clientID |-> "clientIDChainB"]
        remoteEnd |-> [connectionID |-> "connBtoA",
                       clientID |-> "clientIDChainA"]
                    
    2. Environment injects, maliciously, a ICS3MsgInit to chain B with
    the following parameters:

        localEnd |-> [connectionID |-> "connBtoA",
                      clientID |-> "clientIDChainA"]
        remoteEnd |-> [connectionID |-> "connBtoA",
                       clientID |-> "clientIDChainA"]
                       
    Notice that the localEnd is correct, so chain B will validate and
    process this message; the remoteEnd is incorrect, however, but chain
    B is not able to validate that part of the connection, so it will
    accept it as it is.
    
    2. Chain A processes the ICS3MsgInit (action HandleInitMsg) and
    updates its store.connection with the parameters from step 1 above.
    At this point, chain A "locks onto" these parameters and will not
    accept any others. Chain A also produces a ICS3MsgTry message.
    
    3. Chain B processes the ICS3MsgInit (action HandleInitMsg) and
    updates its store.connection with the parameters from step 2 above.
    Chain B "locks onto" these parameters and will not accept any others.
    At this step, chain B produces a ICS3MsgTry message with the local
    parameters from its connection.
    
    Both chains will be locked on a different set of connection parameters,
    and neither chain will accept their corresponding ICS3MsgTry, hence a
    deadlock. To avoid this problem, we prevent the environment from
    acting maliciously in the preliminary parts of the ICS3 protocol, until
    both chains finish locking on the same set of connection parameters.
    
 *)
InitEnv ==
    /\ maliciousEnv = FALSE
    /\ \/ /\ bufChainA \in {<<msg>> : (* ICS3MsgInit to chain A. *)
            msg \in InitMsgs(chmA!ConnectionEnds, chmB!ConnectionEnds)}
          /\ bufChainB = <<>>
       \/ /\ bufChainB \in {<<msg>> : (* ICS3MsgInit to chain B. *)
            msg \in InitMsgs(chmB!ConnectionEnds, chmA!ConnectionEnds)}
          /\ bufChainB = <<>>
       \/ /\ bufChainA \in {<<msg>> : (* ICS3MsgInit to both chains. *)
            msg \in InitMsgs(chmA!ConnectionEnds, chmB!ConnectionEnds)}
          /\ bufChainB \in {<<msg>> :
            msg \in InitMsgs(chmB!ConnectionEnds, chmA!ConnectionEnds)}


(* Default next (good) action for Environment.

    May change either of the store of chain A or B. 
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


(* Environment malicious behavior.

    The environment injects a msg. in the buffer of one of the chains. 
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



(* Environment next action.

    There are four possible actions that the environment may perform:
    
    1. A good step: the environment advances or updates the client on
    one of the two chains.
    
    2. The environment becomes malicious, as a result of both chains
    advancing past the UNINIT step (i.e., after both chains finished 
    locking on to a set of connection parameters).
    
    3. A malicious step.
    
    4. The environment stops acting maliciously.
 *)
NextEnv ==
    \/ /\ GoodNextEnv                               (* A good step. *)
       /\ UNCHANGED<<bufChainA, bufChainB, maliciousEnv>>
    \/ /\ maliciousEnv = FALSE                      (* Enable malicious env. *)
       /\ storeChainA.connection.state # "UNINIT"
       /\ storeChainB.connection.state # "UNINIT"
       /\ maliciousEnv' = TRUE
       /\ MaliciousNextEnv
       /\ UNCHANGED chainStoreVars
    \/ /\ maliciousEnv = TRUE                       (* A malicious step. *)
       /\ MaliciousNextEnv
       /\ UNCHANGED<<maliciousEnv, chainStoreVars>>
    \/ /\ maliciousEnv = TRUE                       (* Disable malicious env. *)
       /\ maliciousEnv' = FALSE
       /\ UNCHANGED<<bufChainA, bufChainB, chainStoreVars>>


(* Enables when the connection is open on both chains.

    State predicate signaling that the protocol terminated correctly.
 *)
ICS3ReachTermination ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED <<allVars>>


(* Enables when both chains attain maximum height, if the connection is still
    not opened.

    State predicate signaling that the chains cannot progress any further,
    and therefore the protocol terminates without successfully opening the
    connection.
 *)
ICS3NonTermination ==
    /\ (~ chmA!CanProgress \/ storeChainA.connection.state # "OPEN")
    /\ (~ chmB!CanProgress \/ storeChainB.connection.state # "OPEN")
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
    \/ ICS3ReachTermination
    \/ ICS3NonTermination
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED <<storeChainB, maliciousEnv>>
    \/ chmB!Next /\ UNCHANGED <<storeChainA, maliciousEnv>>


FairProgress ==
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


TypeInvariant ==
    /\ \/ bufChainA \in Seq(ConnectionHandshakeMessages)
       \/ bufChainB \in Seq(ConnectionHandshakeMessages)


(* Liveness property. *)
(* If both chains CanProgress: We should reach open & open. *)
Termination ==
    [](chmA!CanProgress /\ chmB!CanProgress)
        => <> [](/\ storeChainA.connection.state = "OPEN"
                 /\ storeChainB.connection.state = "OPEN")


(* Safety property. *)
ConsistencyProperty ==
    /\ storeChainA.connection.state # "UNINIT"
    /\ storeChainB.connection.state # "UNINIT"
    (* If the connections in the two chains are not null, then the
        connection parameters must always match.
     *)
    => storeChainA.connection.parameters 
        = chmB!FlipConnectionParameters(storeChainB.connection.parameters)

Consistency ==
    [] ConsistencyProperty

=============================================================================
\* Modification History
\* Last modified Mon May 18 14:28:24 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

