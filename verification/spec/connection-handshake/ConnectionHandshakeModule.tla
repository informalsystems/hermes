--------------------- MODULE ConnectionHandshakeModule ---------------------

EXTENDS Naturals

\* Maximum height of the chain where this module is running.
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
 ***************************************************************************)


\* Validates a ConnectionParameter `para` against an already existing connection.
\* If the connection in the store is `nullConnection`, returns true.
\* Otherwise, returns true if `para` matches the connection in the store, and false otherwise.
ValidConnectionParameters(para) ==
    \/ store.connection = nullConnection
    \/ /\ store.connection /= nullConnection
       /\ store.connection.parameters.localEnd.connectionID = para.localEnd.connectionID   
       /\ store.connection.parameters.remoteEnd.connectionID = para.remoteEnd.connectionID  
       /\ store.connection.parameters.localEnd.clientID = para.localEnd.clientID       
       /\ store.connection.parameters.remoteEnd.clientID = para.remoteEnd.clientID      


\* Given a ConnectionParameters record `para`, this operator returns a new set
\* of parameters where the local and remote ends are flipped (i.e., reversed).
FlipConnectionParameters(para) ==
    [localEnd   |-> para.remoteEnd,
     remoteEnd  |-> para.localEnd]


(***************************************************************************
 Connection Handshake Module actions & operators.
 ***************************************************************************)


\* Handles a `CHMsgInit` message.
HandleInitMsg(m) ==
    (* TODO: add proofs in the THEN branch. *)
    LET res == IF store.connection.state = "UNINIT"
               THEN [nConnection |-> [parameters |-> m.parameters, 
                                      state      |-> "INIT"],
                     oMsg |-> [parameters |-> FlipConnectionParameters(m.parameters),
                               type |-> "CHMsgTry"]]
               ELSE [nConnection |-> store.connection,
                     oMsg |-> noMsg] 
    IN /\ store' = [store EXCEPT !.connection = res.nConnection]
       /\ outMsg' = res.oMsg


HandleTryMsg(m) ==
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
   2. Updates outMsg with a reply message, possibly NoMsg.
 *****)
ProcessConnectionHandshakeMessage(msg) ==
    \/ "CHMsgInit" /\ HandleInitMsg(msg)
    \/ "CHMsgTry"  /\ HandleTryMsg(msg)


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
\* Last modified Fri May 01 17:13:55 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

