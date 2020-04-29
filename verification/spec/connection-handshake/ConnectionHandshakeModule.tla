--------------------- MODULE ConnectionHandshakeModule ---------------------

EXTENDS Naturals, TLC

\* Maximum height of the chain where this moduele is running.
CONSTANT MaxHeight


VARIABLES
    inMsg,      \* A buffer holding any message incoming to the chModule.
    outMsg,     \* A buffer holding any message outbound from the chModule.
    store       \* The local store of the chain running this chModule. 


ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}


(* TODO: constants *)
ConnectionIDs == {"connAtoB", "connBtoA"}
nullConnectionID == "null"


(* TODO: constants *)
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
    ]

nullConnection == [state |-> "UNINIT"]


Heights == 1..MaxHeight


Clients ==
    [   
        clientID : ClientIDs,
        consensusState : Heights
    ]
    
nullClient == [clientID |-> nullClientID]

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


\* Validates a ConnectionParameter `para` against the local store.
\* Returns true if `para` is valid, and false otherwise.
ValidConnectionParameters(para) ==
    /\ para.localEnd.connectionID   = GetLocalConnectionID(store.id)
    /\ para.remoteEnd.connectionID  = GetRemoteConnectionID(store.id)
    /\ para.localEnd.clientID       = GetLocalClientID(store.id)
    /\ para.remoteEnd.clientID      = GetRemoteClientID(store.id)


\* Given a ConnectionParameters record `para`, this operator returns a new set
\* of parameters where the local and remote ends are flipped (i.e., reversed).
FlipConnectionParameters(para) ==
    [localEnd   |-> para.remoteEnd,
     remoteEnd  |-> para.localEnd]


(***************************************************************************
 Connection Handshake Module actions.
 ***************************************************************************)


\* Handles a `CHMsgInit` message. 
handleInitMsg(m) ==
    IF store.connection.state = "UNINIT"
        THEN [nConnection   |-> [parameters |-> m.parameters, 
                                 state      |-> "INIT"],
                    (* Asemble the outbound message, type: HandshakeTry *)
              oMsg          |-> [parameters |-> FlipConnectionParameters(m.parameters),
                                 type       |-> "CHMsgTry"]]
                      (* TODO: add proofs here. *)
        ELSE [nConnection   |-> store.connection,
              oMsg          |-> noMsg]


handleTryMsg(m) ==
    (**** TODO ****)
    [nConnection |-> store.connection,
     oMsg        |-> noMsg ]


\* If MaxHeight is not yet reached, then advance the height of the chain. 
AdvanceChainHeight ==
    /\ store.height < MaxHeight
    /\ store' = [store EXCEPT !.height = @ + 1]
    /\ UNCHANGED <<outMsg, inMsg>>


(******
 Expects a valid ConnectionHandshakeMessage record.
 Does two basic actions:
   1. Updates the chain store, and
   2. Updates outMsg with a reply message.
 *****)
ProcessConnectionHandshakeMessage(msg) ==
    LET res == CASE msg.type = "CHMsgInit" -> handleInitMsg(msg)
                 [] msg.type = "CHMsgTry"  -> handleTryMsg(msg)
    IN /\ PrintT([msg |-> res])
       /\ store' = [store EXCEPT !.connection = res.nConnection]
       /\ outMsg' = res.oMsg


\* Generic handle for any type of inbound message.
\* Assumes that 'inMsg' is not empty.
\* Takes care of changing the 'store' and 'outMsg'. 
ProcessInMsg ==
    /\ IF ValidConnectionParameters(inMsg.parameters) = TRUE
        THEN ProcessConnectionHandshakeMessage(inMsg)
        \* The connection parameters are not valid. No state transition.
        ELSE /\ outMsg' = noMsg \* No reply.
             /\ UNCHANGED store
    /\ inMsg' = noMsg \* Flush the inbound message buffer.




(***************************************************************************
 Connection Handshake Module main spec.
 ***************************************************************************)

Init(chainID) ==
    store = [id                 |-> chainID,
             height             |-> 1,
             connection         |-> nullConnection,
             client             |-> nullClient]


Next ==
    IF inMsg /= noMsg
        THEN ProcessInMsg
        \* We have no input message, nothing for us to do.
        ELSE UNCHANGED <<store, inMsg, outMsg>>


=============================================================================
\* Modification History
\* Last modified Wed Apr 29 15:47:07 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

