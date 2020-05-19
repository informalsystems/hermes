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


(************* chainAConnectionEnds & chainBConnectionEnds *****************

    The set of records that each chain can use as a valid local connection
    end. For each chain, this set contains one record, since we are
    modeling a single connection in this specification.
 
 ***************************************************************************)
chainAConnectionEnds == 
    [
        connectionID : { "connAtoB" },
        clientID : { "clientOnAToB" }
    ]
chainBConnectionEnds ==
    [
        connectionID : { "connBtoA" },
        clientID : { "clientOnBToA" }
    ]

AllConnectionEnds ==
    chainAConnectionEnds \union chainBConnectionEnds

AllClientIDs == 
    { x.clientID : x \in AllConnectionEnds }

AllConnectionIDs ==
    { x.connectionID : x \in AllConnectionEnds }


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


INSTANCE ICS3Types

chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- bufChainA,
             outBuf         <- bufChainB,
             store          <- storeChainA,
             ConnectionIDs  <- { x.connectionID : x \in chainAConnectionEnds },
             ClientIDs      <- { x.clientID : x \in chainAConnectionEnds }


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- bufChainB,      (* Flip message buffers *)
             outBuf         <- bufChainA,      (* Inbound of "A" is outbound of "B". *)
             store          <- storeChainB,
             ConnectionIDs  <- { x.connectionID : x \in chainBConnectionEnds },
             ClientIDs      <- { x.clientID : x \in chainBConnectionEnds }


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
            msg \in InitMsgs(chainAConnectionEnds, chainBConnectionEnds)}
          /\ bufChainB = <<>>
       \/ /\ bufChainB \in {<<msg>> : (* ICS3MsgInit to chain B. *)
            msg \in InitMsgs(chainBConnectionEnds, chainAConnectionEnds)}
          /\ bufChainB = <<>>
       \/ /\ bufChainA \in {<<msg>> : (* ICS3MsgInit to both chains. *)
            msg \in InitMsgs(chainAConnectionEnds, chainBConnectionEnds)}
          /\ bufChainB \in {<<msg>> :
            msg \in InitMsgs(chainBConnectionEnds, chainAConnectionEnds)}


(* Default next (good) action for Environment.

    May change either of the store of chain A or B. 
 *)
GoodNextEnv ==
    \/ /\ chmA!CanAdvance
       /\ \/ chmA!AdvanceChainHeight
          \/ chmA!UpdateClient(storeChainB.latestHeight)
       /\ UNCHANGED storeChainB
    \/ /\ chmB!CanAdvance
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
\*    \/ /\ ~ maliciousEnv                            (* Enable malicious env. *)
\*       /\ storeChainA.connection.state # "UNINIT"
\*       /\ storeChainB.connection.state # "UNINIT"
\*       /\ maliciousEnv' = TRUE
\*       /\ MaliciousNextEnv
\*       /\ UNCHANGED chainStoreVars
    \/ /\ maliciousEnv                              (* A malicious step. *)
       /\ MaliciousNextEnv
       /\ UNCHANGED<<maliciousEnv, chainStoreVars>>
    \/ /\ maliciousEnv                              (* Disable malicious env. *)
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
    /\ (~ chmA!CanAdvance \/ storeChainA.connection.state # "OPEN")
    /\ (~ chmB!CanAdvance \/ storeChainB.connection.state # "OPEN")
    /\ UNCHANGED <<allVars>>


(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID and a client. *)
Init ==
    /\ \E clientA \in InitClients({ x.clientID : x \in chainAConnectionEnds }) :
            chmA!Init("chainA", clientA, NullConnection)
    /\ \E clientB \in InitClients({ x.clientID : x \in chainBConnectionEnds }) :
            chmB!Init("chainB", clientB, NullConnection)
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
    /\ \A height \in 1..MaxHeight : WF_storeChainA(chmA!UpdateClient(height))
    /\ \A height \in 1..MaxHeight : WF_storeChainB(chmB!UpdateClient(height))
    /\ WF_storeChainA(chmA!AdvanceChainHeight)
    /\ WF_storeChainB(chmB!AdvanceChainHeight)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


TypeInvariant ==
    /\ chmA!TypeInvariant
    /\ chmB!TypeInvariant


(* Liveness property.
    
    If both chains can progress, we should reach open on both chains.
*)
\*Termination ==
\*\*    [](chmA!CanAdvance /\ chmB!CanAdvance)
\*\*        =>
\*        <> (/\ storeChainA.connection.state = "OPEN"
\*            /\ storeChainB.connection.state = "OPEN"
\*            /\ bufChainA = <<>>
\*            /\ bufChainB = <<>>
\*            /\ chmA!CanAdvance
\*            /\ chmB!CanAdvance
\*            /\ storeChainA.client = storeChainB.client )


MockProperty ==
    <> /\ storeChainA.latestHeight = 3


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

=============================================================================
\* Modification History
\* Last modified Tue May 19 11:35:41 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

