--------------------- MODULE ConnectionHandshakeModule ---------------------

EXTENDS Naturals, FiniteSets, Sequences


CONSTANTS MaxHeight,        \* Maximum height of the local chain.
          ConnectionIDs,    \* The set of all possible connection IDs.
          ClientIDs,        \* The set of all possible client IDs.
          MaxBufLen         \* Maximum length of the input and output buffers.


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


(* The set of all types which a message can take. 
    
    TODO: These types are also used in the Environment module.
    Is it possible to restrict these to a single module? 
 *)
CHMessageTypes ==
    { "CHMsgInit", "CHMsgTry", "CHMsgAck", "CHMsgConfirm"}


(***************************************************************************
 Helper operators.
 ***************************************************************************)

(* Returns true if 'para' matches the parameters in the local connection,
    and returns false otherwise.
 *)
CheckLocalParameters(para) ==
    LET local == store.connection.parameters.localEnd
        remote == store.connection.parameters.remoteEnd 
    IN /\ local.connectionID = para.localEnd.connectionID   
       /\ remote.connectionID = para.remoteEnd.connectionID
       /\ local.clientID = para.localEnd.clientID       
       /\ remote.clientID = para.remoteEnd.clientID


(* Validates a ConnectionParameter.
    Expects as input a ConnectionParameter 'para' and returns true or false.
    
    This is a basic validation step, making sure that 'para' is valid with
    respect to module-level constants ConnectionIDs and ClientIDs.
    If there is a connection in the store, this also validates 'para'
    against the parameters of an existing connection by relying on the
    state predicate CheckLocalParameters.
*)
ValidConnectionParameters(para) ==
    /\ para.localEnd.connectionID \in ConnectionIDs
    /\ para.localEnd.clientID \in ClientIDs
    /\ \/ store.connection = nullConnection
       \/ /\ store.connection /= nullConnection
          /\ CheckLocalParameters(para)


ValidMessageType(type) ==
    /\ type \in CHMessageTypes


\* Given a ConnectionParameters record `para`, this operator returns a new set
\* of parameters where the local and remote ends are flipped (i.e., reversed).
FlipConnectionParameters(para) ==
    [localEnd   |-> para.remoteEnd,
     remoteEnd  |-> para.localEnd]


(* Returns a proof, stating that the local store on this chain comprises a
    connection in a certain state. 
 *)
GetStateProof ==
    [content |-> "state proof content"]


(* TODO *)
GetClientProof ==
    [content |-> "client proof content"]


(***************************************************************************
 Connection Handshake Module actions & operators.
 ***************************************************************************)


(* Drops a message without any priming of local variables. 
    This action always enables (returns true); use with care.
    This action is analogous to "abortTransaction" function from ICS specs.
 *)
DropMsg(m)  ==
    UNCHANGED<<outBuf, store>>


(* Handles a "CHMsgInit" message 'm'.
    
    Primes the store.connection to become initialized with the parameters
    specified in 'm'. Also creates a reply message, enqueued on the outgoing
    buffer.
 *)
HandleInitMsg(m) ==
    /\ store.connection.state = "UNINIT"
    /\ Len(outBuf) < MaxBufLen  \* Enabled if we can reply to the remote chain.
    /\ LET newCon == [parameters |-> m.parameters, 
                      state      |-> "INIT"]
           sProof == GetStateProof
           cProof == GetClientProof
           replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                        type |-> "CHMsgTry",
                        stateProof |-> sProof,
                        clientProof |-> cProof]
       IN /\ outBuf' = Append(outBuf, replyMsg)
          /\ store' = [store EXCEPT !.connection = newCon]


(* Handles a "CHMsgTry" message.
 *)
HandleTryMsg(m) ==
    (* The good-case path. *)
    /\ \/ store.connection.state = "UNINIT"
       \/ store.connection.state = "INIT" /\ CheckLocalParameters(m.parameters)
    /\ Len(outBuf) < MaxBufLen
    /\ LET newCon == [parameters |-> m.parameters, 
                      state |-> "INIT"]
           sProof == GetStateProof
           cProof == GetClientProof
           replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                        type |-> "CHMsgAck"]
       IN /\ outBuf' = Append(outBuf, replyMsg)
          /\ store' = [store EXCEPT !.connection = newCon]


(* Handles a "CHMsgAck" message.
 *)
HandleAckMsg(m) ==
    /\ \/ store.connection.state = "INIT"
       \/ store.connection.state = "TRYOPEN"
    /\ CheckLocalParameters(m.parameters)
    /\ Len(outBuf) < MaxBufLen
    /\ LET newCon == [parameters |-> m.parameters, 
                      state |-> "INIT"]
           sProof == GetStateProof
           cProof == GetClientProof
           replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                        type |-> "CHMsgAck"]
       IN /\ outBuf' = Append(outBuf, replyMsg)
          /\ store' = [store EXCEPT !.connection = newCon]


(* Handles a "CHMsgConfirm" message.
 *)
HandleConfirmMsg(m) ==
    UNCHANGED<<outBuf, store>>


\* If MaxHeight is not yet reached, then advance the height of the chain. 
AdvanceChainHeight ==
    /\ store.height < MaxHeight
    /\ store' = [store EXCEPT !.height = @ + 1]
    /\ UNCHANGED <<outBuf, inBuf>>


(* Generic action for handling any type of inbound message.
    Expects as parameter a message.
    Takes care of invoking priming the 'store' and any reply msg in 'outBuf'.
 *)
ProcessMsg(m) ==
    /\ ValidConnectionParameters(m.parameters) = TRUE
    /\ ValidMessageType(m.type) = TRUE
    (* One of the following disjunctions will always enable, since
        the message type is guaranteed to be valid in the THEN branch. *)
    /\ \/ m.type = "CHMsgInit" /\ HandleInitMsg(m)
       \/ m.type = "CHMsgTry" /\ HandleTryMsg(m)
       \/ m.type = "CHMsgAck" /\ HandleAckMsg(m)
       \/ m.type = "CHMsgConfirm" /\ HandleConfirmMsg(m)


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
    IN /\ inBuf # <<>>         \* Enabled if we have an inbound msg.
       /\ inBuf' = Tail(inBuf) \* Strip the head of our inbound msg. buffer.
       /\ \/ ProcessMsg(m)     \* Generic action for handling a msg.
          \/ DropMsg(m)


=============================================================================
\* Modification History
\* Last modified Tue May 12 13:23:17 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

