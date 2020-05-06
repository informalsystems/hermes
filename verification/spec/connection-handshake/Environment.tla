---------------------------- MODULE Environment ----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC


CONSTANT MaxHeight,     \* Maximum height of any chain in the system.
         MaxBufLen      \* Length (size) of message buffers.

ASSUME MaxHeight > 1
ASSUME MaxBufLen > 1


VARIABLES
    bufChainA,      \* A buffer (sequence) for messages inbound to chain A.
    bufChainB,      \* A buffer for messages inbound to chain B.
    storeChainA,    \* The local store of chain A.
    storeChainB,    \* The local store of chain B.
    stillMalicious  \* If TRUE, environment interferes w/ CH protocol. 


chainAParameters == [
    connectionID |-> { "connAtoB" },
    clientID |-> { "clientChainA" }
]

chainBParameters == [
    connectionID |-> { "connBtoA" },
    clientID |-> { "clientChainB" }
]


ClientIDs == { chainAParameters.clientID, chainBParameters.clientID }
ConnectionIDs == { chainAParameters.connectionID, chainBParameters.connectionID }

chainAVars == <<bufChainA, bufChainB, storeChainA>>
chainBVars == <<bufChainA, bufChainB, storeChainB>>
chainStoreVars == <<storeChainA, storeChainB>>
allVars == <<chainStoreVars, bufChainA, bufChainB, stillMalicious>>


chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inBuf          <- bufChainA,
             outBuf         <- bufChainB,
             store          <- storeChainA,
             ConnectionIDs  <- chainAParameters.connectionID,
             ClientIDs      <- chainAParameters.clientID


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inBuf          <- bufChainB,      \* Flip the message buffers w.r.t. chain A buffers.
             outBuf         <- bufChainA,      \* Inbound for "A" is outbound for "B".
             store          <- storeChainB,
             ConnectionIDs  <- chainBParameters.connectionID,
             ClientIDs      <- chainBParameters.clientID


ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}


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
     stateProof : Proofs,
     clientProof : Proofs]
    \union
    [type : {"CHMsgAck"},
     parameters : ConnectionParameters,
     stateProof : Proofs,
     clientProof : Proofs]
     \union
    [type : {"CHMsgConfirm"},
     parameters : ConnectionParameters,
     stateProof : Proofs]


(* The set of all Init messages, such that the local end is the
    set 'le', and the remote end is set 're'. *)
InitMsgs(le, re) ==
    [type : {"CHMsgInit"},
     parameters : [localEnd : le,
                   remoteEnd : re]]


(* TODO: find a more elegant way to do this. 
    What we want, ideally, is to specify this:
        z \in x
    to obtain a random Sequence z out of a set of sequences x, obtaining:
        bufChainA \in InitMsgs
    instead of the awkward lines for building bufChainA and bufChainB below.
 *)
ChooseInitMsg(le, re) ==
    CHOOSE x \in InitMsgs(le, re) : TRUE


(***************************************************************************
 Environment actions.
 ***************************************************************************)


InitEnv ==
    /\ stillMalicious = TRUE
    (* Assign a sequence (a function) with 1 element -- the Init msg -- to bufChainA. *)
    /\ \/ /\ bufChainA \in {<<msg>> : msg \in InitMsgs(chmA!ConnectionEnds, chmB!ConnectionEnds)}
          /\ bufChainB = <<>>   \* Empty buffer.
       \/ /\ bufChainB \in {<<msg>> : msg \in InitMsgs(chmB!ConnectionEnds, chmA!ConnectionEnds)}
          /\ bufChainA = <<>>


(* The environment overwrites the buffer of one of the chains. 
   This interferes with the CH protocol in two ways:
    1. by introducing additional messages that are incorrect,
    2. by dropping correct messages (overwritting them).
 *)
MaliciousNextEnv ==
    (* Without the first constraint, Env could fill buffers (DoS attack). *)
    \/ /\ Len(bufChainA) < MaxBufLen - 1
       /\ bufChainA' \in 
            {Append(bufChainA, arbitraryMsg) : 
                arbitraryMsg \in ConnectionHandshakeMessages} 
       /\ UNCHANGED bufChainB
    \/ /\ Len(bufChainA) < MaxBufLen - 1
       /\ bufChainB' \in
            {Append(bufChainB, arbitraryMsg) :
                arbitraryMsg \in ConnectionHandshakeMessages}
       /\ UNCHANGED bufChainA


NextEnv ==
    \/ /\ stillMalicious = TRUE
       /\ MaliciousNextEnv
       /\ UNCHANGED stillMalicious
    \/ /\ stillMalicious = TRUE
       /\ stillMalicious' = FALSE
       /\ UNCHANGED<<bufChainA, bufChainB>>


CHDone ==
    /\ storeChainA.connection.state = "INIT" (* TODO: should be OPEN *)
    /\ storeChainB.connection.state = "INIT"
    /\ UNCHANGED <<allVars>>

(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)


Init ==
    /\ chmA!Init("chainA")
    /\ chmB!Init("chainB")
    /\ InitEnv



\* The two CH modules and the environment alternate their steps.
Next ==
    \/ CHDone
    \/ NextEnv /\ UNCHANGED <<chainStoreVars>>
    \/ chmA!Next /\ UNCHANGED <<storeChainB, stillMalicious>>
    \/ chmB!Next /\ UNCHANGED <<storeChainA, stillMalicious>>


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)


TypeInvariant ==
    /\ bufChainA \in ConnectionHandshakeMessages
    /\ bufChainB \in ConnectionHandshakeMessages


\* Liveness property.
Termination ==
    <> ~ stillMalicious
        => <> /\ storeChainA.connection.state = "INIT" (* TODO: should be OPEN *)
              /\ storeChainB.connection.state = "INIT"


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
\* Last modified Wed May 06 16:41:45 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

