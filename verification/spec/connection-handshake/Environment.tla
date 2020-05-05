---------------------------- MODULE Environment ----------------------------

EXTENDS Naturals, FiniteSets


CONSTANT MaxHeight     \* Maximum height of any chain in the system.


VARIABLES
    bufChainA,      \* A buffer for messages inbound to chain A.
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
             inMsg          <- bufChainA,
             outMsg         <- bufChainB,
             store          <- storeChainA,
             ConnectionIDs  <- chainAParameters.connectionID,
             ClientIDs      <- chainAParameters.clientID
             


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight      <- MaxHeight,
             inMsg          <- bufChainB,      \* Flip the message buffers w.r.t. chain A buffers.
             outMsg         <- bufChainA,      \* Inbound for "A" is outbound for "B".
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
     parameters : ConnectionParameters
\*        stateProof : Proofs,
\*        consensusHeight : Proofs
    ]


(***************************************************************************
 Environment actions.
 ***************************************************************************)

InitMsg(le, re) ==
    [type |-> "CHMsgInit",
     parameters |-> [localEnd |-> le,
                     remoteEnd |-> re]]


InitEnv ==
    /\ stillMalicious = TRUE
    /\ \/ /\ bufChainA = InitMsg(chmA!ChooseLocalEnd, chmB!ChooseLocalEnd) 
          /\ bufChainB = chmB!NoMsg
       \/ /\ bufChainB = InitMsg(chmB!ChooseLocalEnd, chmA!ChooseLocalEnd) 
          /\ bufChainA = chmA!NoMsg


(* The environment overwrites the buffer of one of the chains. 
   This interferes with the CH protocol in two ways:
    1. by introducing additional messages that are incorrect,
    2. by dropping correct messages (overwritting them).
 *)
MaliciousNextEnv ==
    \/ /\ bufChainA' \in ConnectionHandshakeMessages
       /\ UNCHANGED bufChainB 
    \/ /\ bufChainB' \in ConnectionHandshakeMessages
       /\ UNCHANGED bufChainA


NextEnv ==
    \/ /\ stillMalicious
       /\ MaliciousNextEnv
       /\ UNCHANGED stillMalicious
    \/ /\ stillMalicious
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
    /\ InitEnv
    /\ chmA!Init("chainA")
    /\ chmB!Init("chainB")


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
\* Last modified Tue May 05 16:34:19 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

