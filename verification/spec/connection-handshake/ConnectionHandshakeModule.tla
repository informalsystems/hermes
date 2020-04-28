--------------------- MODULE ConnectionHandshakeModule ---------------------

EXTENDS Naturals, TLC

\* Maximum height of the chain where this moduele is running.
CONSTANT MaxHeight


VARIABLES
    inMsg,      \* A buffer holding any message incoming to the chModule.
    outMsg,     \* A buffer holding any message outbound from the chModule.
    store       \* The local store of the chain running this chModule. 



ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

ConnectionIDs == {"connAtoB", "connBtoA"}
nullConnectionID == "null"

ClientIDs == { "clientA", "clientB" }
nullClientID == "null"

ConnectionEnds ==
    [
        connectionID : ConnectionIDs,
        clientID : ClientIDs
        \* commitmentPrefix add later
    ]

ConnectionParameters ==
    [
        localEnd : ConnectionEnds,
        remoteEnd : ConnectionEnds
    ]

Connections ==
    [
        parameters : ConnectionParameters,
        state : ConnectionStates
        \* any other fields that are specific for a connection
    ]

nullConnection == "null"


(******************************** Messages ********************************
These messages are connection handshake specific.
 ***************************************************************************)
ConnectionHandshakeMessages ==
    [type : {"ConnOpenInit"}, 
     parameters : ConnectionParameters]
    \union
    [type : {"ConnOpenTry"},
     parameters : ConnectionParameters
\*        stateProof : Proofs, 
\*        consensusHeight : Proofs
    ]

noMsg == [ type |-> "none" ]


(***************************************************************************
 Helper operators.
 Partly cf. ibc-rs/#55.
 ***************************************************************************)


GetLocalConnectionID(chainID) ==
    IF chainID = "chainA"
        THEN "connAtoB"
        ELSE IF chainID = "chainB"
                THEN "connBtoA"
                ELSE nullConnectionID      


\* get the connection ID of the connection end at chainID's counterparty chain
GetRemoteConnectionID(chainID) ==
    IF chainID = "chainA"
        THEN "connBtoA"
        ELSE IF chainID = "chainB"
                THEN "connAtoB"
                ELSE nullConnectionID


GetLocalClientID(chainID) ==
    IF chainID = "chainA"
        THEN "clientA"
        ELSE IF chainID = "chainB"
                THEN "clientB"
                ELSE nullClientID      


\* get the connection ID of the connection end at chainID's counterparty chain
GetRemoteClientID(chainID) ==
    IF chainID = "chainA"
        THEN "clientB"
        ELSE IF chainID = "chainB"
                THEN "clientA"
                ELSE nullClientID


validConnectionParameters(para) ==
    /\ para.localEnd.connectionID = GetLocalConnectionID(store.id)
    /\ para.remoteEnd.connectionID = GetRemoteConnectionID(store.id)
    /\ para.localEnd.clientID = GetLocalClientID(store.id)
    /\ para.remoteEnd.clientID = GetRemoteClientID(store.id)
    /\ TRUE


(***************************************************************************
 Connection Handshake Module actions.
 ***************************************************************************)


handleInitMsg ==
    /\ inMsg.type = "ConnOpenInit"
    /\ [newState   |-> TRUE,
        outMsg     |-> noMsg ]


handleTryMsg ==
    /\ inMsg.type = "ConnOpenTry"
    /\ store.connection.state \in {"UNINIT", "INIT", "TRYOPEN"}
    /\ [newState |-> TRUE,
        outMsg   |-> noMsg ]


\* If MaxHeight is not yet reached, then advance the height of the chain. 
advanceChainHeight ==
    /\ PrintT([msg |-> "in advanceChainHeight", id |-> store.id])
    /\ store.height < MaxHeight
    /\ store' = [store EXCEPT !.height = @ + 1]
    /\ UNCHANGED <<outMsg, inMsg>>


\* Generic handle for any time of inbound message. 
handleInMsg ==
    /\ PrintT([msg |-> "handleInMsg", id |-> store.id])
    /\ inMsg /= noMsg
    /\ IF validConnectionParameters(inMsg.parameters) = TRUE
        \* The connection parameters are valid. Handle the message.
        THEN LET res == \/ handleInitMsg
                        \/ handleTryMsg
             IN /\ store' = res.newState
                /\ outMsg' = res.outMsg
                /\ inMsg' = noMsg   
        \* The connection parameters are not valid. No state transition.
        ELSE /\ inMsg' = noMsg
             /\ outMsg' = noMsg
             /\ UNCHANGED store


(***************************************************************************
 Connection Handshake Module main spec.
 ***************************************************************************)

Init(chainID) ==
    store = [id                 |-> chainID,
             height             |-> 1,
             connection         |-> nullConnection ]


Next ==
    \/ advanceChainHeight
    \/ handleInMsg

=============================================================================
\* Modification History
\* Last modified Tue Apr 28 11:18:22 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

