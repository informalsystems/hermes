--------------------- MODULE ConnectionHandshakeModule ---------------------

EXTENDS Naturals


CONSTANTS MaxHeight,    \* Maximum height of the chain where this module runs.
          ConnectionIDs,\* The set of all possible connection IDs.
          ClientIDs     \* The set of all possible client IDs.


VARIABLES
    inMsg,      \* A buffer holding any message incoming to the chModule.
    outMsg,     \* A buffer holding any message outbound from the chModule.
    store       \* The local store of the chain running this chModule. 


ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}


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

nullClient == "no client"

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

NoMsg == [ type |-> "none" ]
     

(***************************************************************************
 Helper operators.
 ***************************************************************************)


\* Validates a ConnectionParameter `para` against an already existing connection.
\* If the connection in the store is `nullConnection`, returns true.
\* Otherwise, returns true if `para` matches the connection in the store, and false otherwise.
ValidConnectionParameters(para) ==
    /\ para.localEnd.connectionID \in ConnectionIDs
    /\ para.localEnd.clientID \in ClientIDs
    /\ \/ store.connection = nullConnection
       \/ /\ store.connection /= nullConnection
           /\ store.connection.parameters.localEnd.connectionID = para.localEnd.connectionID   
           /\ store.connection.parameters.remoteEnd.connectionID = para.remoteEnd.connectionID
           /\ store.connection.parameters.localEnd.clientID = para.localEnd.clientID       
           /\ store.connection.parameters.remoteEnd.clientID = para.remoteEnd.clientID      

(* The initialization message that this module expects  *)
InitMsg ==
    CHOOSE m \in ConnectionHandshakeMessages :
        /\ m.type = "CHMsgInit"
        /\ m.parameters.localEnd.connectionID \in ConnectionIDs
        /\ m.parameters.localEnd.clientID \in ClientIDs


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
                     oMsg |-> NoMsg] 
    IN /\ store' = [store EXCEPT !.connection = res.nConnection]
       /\ outMsg' = res.oMsg


HandleTryMsg(m) ==
    (* TODO: add proofs & more logic. *)
    LET res == IF store.connection.state = "UNINIT"
               THEN [nConnection |-> [parameters |-> m.parameters, 
                                      state      |-> "INIT"],
                     oMsg |-> [parameters |-> FlipConnectionParameters(m.parameters),
                               type |-> "CHMsgAck"]]
               ELSE [nConnection |-> store.connection,
                     oMsg |-> NoMsg] 
    IN /\ store' = [store EXCEPT !.connection = res.nConnection]
       /\ outMsg' = res.oMsg


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
    \/ msg.type = "CHMsgInit" /\ HandleInitMsg(msg)
    \/ msg.type = "CHMsgTry"  /\ HandleTryMsg(msg)


\* Generic handle for any type of inbound message.
\* Assumes that 'inMsg' is not empty.
\* Takes care of changing the 'store' and 'outMsg'. 
ProcessInMsg ==
    /\ IF ValidConnectionParameters(inMsg.parameters) = TRUE
        THEN ProcessConnectionHandshakeMessage(inMsg)
        \* The connection parameters are not valid. No state transition.
        ELSE /\ outMsg' = NoMsg \* No reply.
             /\ UNCHANGED store
    /\ inMsg' = NoMsg \* Flush the inbound message buffer.


(***************************************************************************
 Connection Handshake Module main spec.
 ***************************************************************************)

Init(chainID) ==
    store = [id                 |-> chainID,
             height             |-> 1,
             connection         |-> nullConnection,
             client             |-> nullClient]


Next ==
    IF inMsg /= NoMsg
        THEN ProcessInMsg
        \* We have no input message, nothing for us to do.
        ELSE UNCHANGED <<store, inMsg, outMsg>>


=============================================================================
\* Modification History
\* Last modified Tue May 05 13:30:21 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

