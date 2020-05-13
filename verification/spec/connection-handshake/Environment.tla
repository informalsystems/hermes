---------------------------- MODULE Environment ----------------------------

(* TODO: clarify the name and purpose of this MODULE in the README.md.
    This spec is wiring everything together. *)

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


chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inBuf          <- bufChainA,
             outBuf         <- bufChainB,
             store          <- storeChainA,
             ConnectionIDs  <- chainAParameters.connectionIDs,
             ClientIDs      <- chainAParameters.clientIDs


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inBuf          <- bufChainB,      \* Flip the message buffers w.r.t. chain A buffers.
             outBuf         <- bufChainA,      \* Inbound for "A" is outbound for "B".
             store          <- storeChainB,
             ConnectionIDs  <- chainBParameters.connectionIDs,
             ClientIDs      <- chainBParameters.clientIDs


ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}


(* TODO BLOCK COMMENTS *)
ConnectionParameters ==
    [
        localEnd : chmA!ConnectionEnds,
        remoteEnd : chmB!ConnectionEnds
    ]

Connections ==
    [
        parameters : ConnectionParameters,
        state : ConnectionStates
    ]

(* This is a mock proof.
    TODO explain *)
Proofs ==
    [
        height : 1..MaxHeight
    ]

(******************************** Messages ********************************
 These messages are connection handshake specific.
 
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
     connProof : Proofs,
     clientProof : Proofs]
    \union
    [type : {"CHMsgAck"},
     parameters : ConnectionParameters,
     connProof : Proofs,
     clientProof : Proofs]
     \union
    [type : {"CHMsgConfirm"},
     parameters : ConnectionParameters,
     connProof : Proofs]


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


(* May change either of the store of chain A or B. *)
GoodNextEnv ==
    \/ chmA!AdvanceChainHeight /\ UNCHANGED storeChainB
    \/ chmB!AdvanceChainHeight /\ UNCHANGED storeChainA
    \/ \E h \in { chmA!Heights } :
            \/ chmA!UpdateClient(h) /\ UNCHANGED storeChainB
            \/ chmB!UpdateClient(h) /\ UNCHANGED storeChainA


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


CHDone ==
    /\ storeChainA.connection.state = "INIT" (* TODO: should be OPEN *)
    /\ storeChainB.connection.state = "INIT"
    /\ UNCHANGED <<allVars>>

(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID as well as a client.
 *)
Init ==
    /\ \E cidA \in chainAParameters.clientIDs :
            chmA!Init("chainA",
                [clientID |-> cidA,
                 consensusStates |-> {}, (* Client state is an empty set. *)
                 latestHeight |-> 0])
    /\ \E cidB \in chainBParameters.clientIDs :
            chmB!Init("chainB",
                [clientID |-> cidB,
                 consensusStates |-> {},
                 latestHeight |-> 0])
    /\ InitEnv


\* The two CH modules and the environment alternate their steps.
Next ==
    \/ CHDone
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED <<storeChainB, maliciousEnv>>
    \/ chmB!Next /\ UNCHANGED <<storeChainA, maliciousEnv>>


FairModuleProgress ==
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)

Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairModuleProgress


(* TODO: Unclear how to capture the type of a sequence. *)
\*TypeInvariant ==
\*    /\ \/ bufChainA = <<>>
\*       \/ \A e in bufChainA : e \in ConnectionHandshakeMessages
\*    /\ bufChainB \in ConnectionHandshakeMessages


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
\* Last modified Wed May 13 16:11:41 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

