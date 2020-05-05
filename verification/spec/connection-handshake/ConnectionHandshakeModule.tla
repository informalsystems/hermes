--------------------- MODULE ConnectionHandshakeModule ---------------------

EXTENDS Naturals, FiniteSets, Sequences


CONSTANTS MaxHeight,    \* Maximum height of the chain where this module runs.
          ConnectionIDs,\* The set of all possible connection IDs.
          ClientIDs,    \* The set of all possible client IDs.
          MaxBufLen     \* Maximum length of the input and output buffers.


ASSUME Cardinality(ConnectionIDs) >= 1
ASSUME Cardinality(ClientIDs) >= 1


VARIABLES
    inBuf,      \* A buffer (Sequence) holding any message(s) incoming to the chModule.
    outBuf,     \* A buffer (Sequence) holding outbound message(s) from the chModule.
    store       \* The local store of the chain running this chModule. 


ConnectionEnds ==
    [
        connectionID : ConnectionIDs,
        clientID : ClientIDs
        \* commitmentPrefix add later
    ]


nullConnection == [state |-> "UNINIT"]


Heights == 1..MaxHeight


Clients ==
    [   
        clientID : ClientIDs,
        consensusState : Heights
    ]

nullClient == "no client"


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
ChooseLocalEnd ==
    CHOOSE l \in ConnectionEnds : TRUE


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
       /\ outBuf' = Append(outBuf, res.oMsg)


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
       /\ outBuf' = res.oMsg


\* If MaxHeight is not yet reached, then advance the height of the chain. 
\*AdvanceChainHeight ==
\*    /\ store.height < MaxHeight
\*    /\ store' = [store EXCEPT !.height = @ + 1]
\*    /\ UNCHANGED <<outBuf, inBuf>>


(******
 Expects a valid ConnectionHandshakeMessage record.
 Does two basic actions:
   1. Updates the chain store, and
   2. Updates outBuf with a reply message, possibly NoMsg.
 *****)
ProcessConnectionHandshakeMsg(msg) ==
    \/ msg.type = "CHMsgInit" /\ HandleInitMsg(msg)
    \/ msg.type = "CHMsgTry"  /\ HandleTryMsg(msg)


\* Generic handle for any type of inbound message.
\* Expects a parameter a non-null message.
\* Takes care of changing the 'store' and enqueing any reply msg in 'outBuf'.
ProcessMsg(m) ==
    IF ValidConnectionParameters(m.parameters) = TRUE
    THEN ProcessConnectionHandshakeMsg(m)
    \* The connection parameters are not valid. No state transition.
    ELSE UNCHANGED<<store, outBuf>>
(* TODO: structure this ^^ logic better using LET .. IN *)


(***************************************************************************
 Connection Handshake Module main spec.
 ***************************************************************************)


Init(chainID) ==
    /\ store = [id |-> chainID,
                height |-> 1,
                connection |-> nullConnection,
                client |-> nullClient]


Next ==
    LET m == Head(inBuf)
    IN /\ inBuf /= <<>>    \* Enabled if we have a message in our inbound buffer.
       /\ Len(outBuf) < MaxBufLen
       /\ ProcessMsg(m)
       /\ inBuf' = Tail(inBuf) \* Remove the head of the inbound message buffer.


=============================================================================
\* Modification History
\* Last modified Tue May 05 18:34:29 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

