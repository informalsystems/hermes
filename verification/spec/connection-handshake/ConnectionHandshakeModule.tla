--------------------- MODULE ConnectionHandshakeModule ---------------------

(***************************************************************************

    This module is part of the TLA+ specification for the
    IBC Connection Handshake (CH) protocol.
    
    This module captures the actions and operators of the IBC CH protocol.
    Typically, it is an IBC module running on a chain that would implement
    this logic, hence the name "ConnectionHandshakeModule".

    This module deals with a high-level spec of the CH protocol, hence it is
    a simplification in several regards:
    - the modules assumes to run on a chain which modeled as a simple
    advancing height, plus a few more critical fields (see the 'store'),
    but without any state (e.g., blockchain, transactions, consensus core);
    - we model a single connection; establishing multiple connections is not
    possible;
    - we do not do any cryptographic proofs or proof verifications.
    - the abstractions we use are higher-level, and slightly different from
    the ones in ICS 003 (see e.g., ConnectionEnd and Connection)
    - the client colocated with the module is simplified, comprising only
    a set of heights.

 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences


CONSTANTS MaxHeight,        \* Maximum height of the local chain.
          ConnectionIDs,    \* The set of all possible connection IDs.
          ClientIDs,        \* The set of all possible client IDs.
          MaxBufLen,        \* Maximum length of the input and output buffers.
          ConnectionStates  \* All the possible connection states.

ASSUME Cardinality(ConnectionIDs) >= 1
ASSUME Cardinality(ClientIDs) >= 1


VARIABLES
(******************************* Store *****************************
     The store record of a chain contains the following fields:
     
     - id -- a string 
       Stores the identifier of the chain where this module executes.

     - latestHeight -- a Nat
       Describes the current height of the chain.  

     - connection -- a connection record.
       Captures all the details of the connection on this chain.
       For a full description of a connection record, see the
       'Environment.Connections' set.

     - client -- a client record.
       Specifies the state of the client running on this chain.
       For a full description of a client and the initialization values
       for this record, see the InitClients set below.  
     
 ***************************************************************************)   
    store,
    inBuf,  \* A buffer (Sequence) holding any message(s) incoming to the chModule.
    outBuf  \* A buffer (Sequence) holding outbound message(s) from the chModule.


vars == <<inBuf, outBuf, store>>


(******************************* ConnectionEnds *****************************
     A set of connection end records.
     A connection end record contains the following fields:
     
     - connectionID -- a string 
       Stores the identifier of this connection, specific to a chain.

     - clientID -- a string
       Stores the identifier of the client running on this chain.  
     
 ***************************************************************************)
ConnectionEnds ==
    [
        connectionID : ConnectionIDs,
        clientID : ClientIDs
    ]


(*
    Initially, the connection on this chain is uninitialized. 
*)
nullConnection == [state |-> "UNINIT"]


(******************************* InitClients *****************************
     A set of records describing the possible initial values for the
     clients on this chain.
     
     A client record contains the following fields:

     - consensusStates -- a set of heights, each height being a Nat 
       Stores the set of all heights (i.e., consensus states) that this
       client observed. At initialization time, the client only observes
       the first height, so the only possible value for this record is
       {1}.

     - clientID -- a string
       The identifier of the client.
       
     - latestHeight -- a natural number
       Stores the latest height among all the heights in consensusStates.
       Initialized to 1.
     
 ***************************************************************************)
InitClients ==
    [   
        consensusStates : {{1}},
        clientID : ClientIDs,
        latestHeight : {1}
    ]


(******************************* ConnProof *********************************

     A set of records describing the possible values for connection proofs.
     
     A connection proof record contains the following fields:

     - connectionState -- a string 
       Captures the state of the connection in the local store of the module
       which created this proof.

     - height -- a Nat
       The current height (latestHeight) of the chain at the moment when the
       module created this proof.

 ***************************************************************************)
ConnProofs ==
    [
        connectionState : ConnectionStates, 
        height : 1..MaxHeight
    ]


(******************************* ClientProofs *******************************

     A set of records describing the possible values for client proofs.
     
     A client proof record contains the following fields:

     - height -- a Nat
       The current height (latestHeight) of the client colocated with module
       which created this proof.

 ***************************************************************************)
ClientProofs ==
    [
        height : 1..MaxHeight
    ]


(******************************* CHMessageTypes *****************************

     The set of valid message types that this module can handle, e.g., as
     incoming or outgoing messages.

     For a complete description of the message record, see
     'Environment.Messages'.
     
 ***************************************************************************)
CHMessageTypes ==
    {"CHMsgInit", 
     "CHMsgTry",
     "CHMsgAck",
     "CHMsgConfirm"}


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


(* Basic validation on the type of an incoming message.
 *)
ValidMessageType(m) ==
    m.type \in CHMessageTypes


(* Basic validation on an incoming message, including the
    connection proof and client proofs.
    
    The following three formulas are state predicates,
    not type invariants! Some proofs are generated by the
    malicious environment, and therefore may be malformed.
    Our specification must be able to capture such malformed
    records, and these state predicates helps filter them out.
 *)
ValidConnProof(m) ==
     m.connProof \in ConnProofs


ValidClientProof(m) ==
     m.clientProof \in ClientProofs


ValidMsg(m) == 
    /\ ValidConnectionParameters(m.parameters)
    /\ ValidMessageType(m)
    /\ \/ m.type = "CHMsgInit"
       \/ m.type = "CHMsgTry" /\ ValidConnProof(m) /\ ValidClientProof(m)
       \/ m.type = "CHMsgAck" /\ ValidConnProof(m) /\ ValidClientProof(m) 
       \/ m.type = "CHMsgConfirm" /\ ValidConnProof(m)


(* Operator for reversing the connection ends.

    Given a ConnectionParameters record 'para', returns a new set
    of parameters where the local and remote ends are
    flipped (i.e., reversed).
 *)
FlipConnectionParameters(para) ==
    [localEnd   |-> para.remoteEnd,
     remoteEnd  |-> para.localEnd]


(* Operator for construcing a connection proof.

    The connection proof is used to demonstrate to another chain that the
    local store on this chain comprises a connection in a certain state. 
 *)
GetConnProof(connState) ==
    [height |-> store.latestHeight,
     connectionState |-> connState]


(* Operator for construcing a client proof.
 *)
GetClientProof ==
    [height |-> store.client.latestHeight]


(* Verification of a connection proof. 

    This is a state predicate returning true if the following holds: the local
    client on this chain stores the height reported in the proof. Note that this
    condition should eventually become true, assuming a correct environment, which
    should periodically update the client on each chain; see actions 'GoodNextEnv'
    and 'UpdateClient'. 
 *)
VerifyConnProof(cp) ==
    /\ cp.height \in store.client.consensusStates 


(* Verification of a client proof.

    This is a state predicate returning true if the following holds: the height
    reported in the client proof must not exceed the current (latestHeight) of
    this chain.
 *)
VerifyClientProof(cp) ==
    cp.height <= store.latestHeight


(***************************************************************************
 Connection Handshake Module actions & operators.
 ***************************************************************************)


(* Drops a message without priming the store or output buffer variables.
 
    This action always enables (returns true); use with care.
    This action is analogous to "abortTransaction" function from ICS specs.
 *)
DropMsg(m) ==
    /\ UNCHANGED<<outBuf, store>>


(* Modifies the local store.

    Replaces the connection in the store with the argument 'newCon'.
    If the height (latestHeight) of the chain has not yet attained MaxHeight, this action also
    advances the chain height. 
 *)
ModifyStore(newCon) ==
    \/ /\ store.latestHeight < MaxHeight
       /\ store' = [store EXCEPT !.connection = newCon,
                                 !.latestHeight = @ + 1]
    \/ /\ store.latestHeight >= MaxHeight
       /\ store' = [store EXCEPT !.connection = newCon]


(* State predicate, guarding the handler for the Init msg. 
 *)
PreconditionsInitMsg(m) ==
    /\ store.connection.state = "UNINIT"


(* Handles a "CHMsgInit" message 'm'.
    
    Primes the store.connection to become initialized with the parameters
    specified in 'm'. Also creates a reply message, enqueued on the outgoing
    buffer.
 *)
HandleInitMsg(m) ==
    (* The good-case path. *)
    \/ /\ PreconditionsInitMsg(m) = TRUE
       /\ Len(outBuf) < MaxBufLen  (* Enables if we can reply on the buffer. *)
       /\ LET newCon == [parameters |-> m.parameters,
                         state      |-> "INIT"]
              sProof == GetConnProof("INIT")
              cProof == GetClientProof
              replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                           type |-> "CHMsgTry",
                           connProof |-> sProof,
                           clientProof |-> cProof]
           IN /\ outBuf' = Append(outBuf, replyMsg)
              /\ ModifyStore(newCon)
    (* The exceptional path. *)
    \/ /\ PreconditionsInitMsg(m) = FALSE
       /\ DropMsg(m)


(* State predicate, guarding the handler for the Try msg.

    If any of these preconditions does not hold, the message
    is dropped. 
 *)
PreconditionsTryMsg(m) ==
    /\ \/ store.connection.state = "UNINIT"
       \/ /\ store.connection.state = "INIT"
          /\ CheckLocalParameters(m.parameters)
    /\ m.connProof.connectionState = "INIT"


(* Handles a "CHMsgTry" message.
 *)
HandleTryMsg(m) ==
    \/ /\ PreconditionsTryMsg(m) = TRUE
       /\ Len(outBuf) < MaxBufLen
       /\ VerifyConnProof(m.connProof)
       /\ VerifyClientProof(m.clientProof)
       /\ LET newCon == [parameters |-> m.parameters, 
                         state |-> "TRYOPEN"]
              sProof == GetConnProof("TRYOPEN")
              cProof == GetClientProof
              replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                           type |-> "CHMsgAck",
                           connProof |-> sProof,
                           clientProof |-> cProof]
          IN /\ outBuf' = Append(outBuf, replyMsg)
             /\ ModifyStore(newCon)
    \/ /\ PreconditionsTryMsg(m) = FALSE
       /\ DropMsg(m)


(* State predicate, guarding the handler for the Ack msg. 
 *)
PreconditionsAckMsg(m) ==
    /\ \/ store.connection.state = "INIT"
       \/ store.connection.state = "TRYOPEN"
    /\ CheckLocalParameters(m.parameters)
    /\ m.connProof.connectionState = "TRYOPEN"


(* Handles a "CHMsgAck" message.
 *)
HandleAckMsg(m) ==
    \/ /\ PreconditionsAckMsg(m) = TRUE
       /\ Len(outBuf) < MaxBufLen
       /\ VerifyConnProof(m.connProof)
       /\ LET newCon == [parameters |-> m.parameters, 
                         state |-> "OPEN"]
              sProof == GetConnProof("OPEN")
              cProof == GetClientProof
              replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                           type |-> "CHMsgConfirm",
                           connProof |-> sProof,
                           clientProof |-> cProof]
          IN /\ outBuf' = Append(outBuf, replyMsg)
             /\ ModifyStore(newCon)
    \/ /\ PreconditionsAckMsg(m) = FALSE
       /\ DropMsg(m)


(* State predicate, guarding the handler for the Confirm msg. 
 *)
PreconditionsConfirmMsg(m) ==
    /\ store.connection.state = "TRYOPEN"
    /\ CheckLocalParameters(m.parameters)
    /\ m.connProof.connectionState = "OPEN"


(* Handles a "CHMsgConfirm" message.
 *)
HandleConfirmMsg(m) ==
    \/ /\ PreconditionsConfirmMsg(m) = TRUE
       /\ VerifyConnProof(m.connProof)
       /\ LET newCon == [parameters |-> m.parameters,
                         state |-> "OPEN"]
          IN /\ ModifyStore(newCon)
             /\ UNCHANGED outBuf    (* We're not sending any reply. *)
    \/ /\ PreconditionsConfirmMsg(m) = FALSE
       /\ DropMsg(m)


(* If MaxHeight is not yet reached, then advance the latestHeight of the chain.
 *) 
AdvanceChainHeight ==
    \/ /\ store.latestHeight < MaxHeight
       /\ store' = [store EXCEPT !.latestHeight = @ + 1]
    \/ /\ store.latestHeight >= MaxHeight
       /\ UNCHANGED store


(* Action for updating the local client on this chain with a new height.
    
    This may prime the store; leaves the chain buffers unchanged.
    This will also advance the chain height unless MaxHeight is reached.
    If the 'height' parameter already exists as part of
    'store.client.consensusStates', then we do not change the store.
 *)
UpdateClient(height) ==
    \/ /\ (height \in store.client.consensusStates)
       /\ UNCHANGED store
    \/ /\ ~ (height \in store.client.consensusStates)
       /\ LET newLHeight == IF height > store.client.latestHeight
                            THEN height
                            ELSE store.client.latestHeight
          IN \/ /\ store.latestHeight < MaxHeight
                /\ store' = [store EXCEPT !.latestHeight = @ + 1,
                                          !.client.consensusStates = @ \cup {height},
                                          !.client.latestHeight = newLHeight]
             \/ /\ store.latestHeight >= MaxHeight
                /\ store' = [store EXCEPT !.client.consensusStates = @ \cup {height},
                                          !.client.latestHeight = newLHeight]


(* Generic action for handling any type of inbound message.

    Expects as parameter a message.
    Takes care of invoking priming the 'store' and any reply msg in 'outBuf'.
    This action assumes the message type is valid, therefore one of the
    disjunctions will always enable.
 *)
ProcessMsg(m) ==
    \/ m.type = "CHMsgInit" /\ HandleInitMsg(m)
    \/ m.type = "CHMsgTry" /\ HandleTryMsg(m)
    \/ m.type = "CHMsgAck" /\ HandleAckMsg(m)
    \/ m.type = "CHMsgConfirm" /\ HandleConfirmMsg(m)


(***************************************************************************
 Connection Handshake Module main spec.
 ***************************************************************************)


Init(chainID, client) ==
    /\ store = [id |-> chainID,
                latestHeight |-> 1,
                connection |-> nullConnection,
                client |-> client]


Next ==
    LET m == Head(inBuf)
    IN /\ inBuf # <<>>         \* Enabled if we have an inbound msg.
       /\ inBuf' = Tail(inBuf) \* Strip the head of our inbound msg. buffer.
       /\ \/ /\ ValidMsg(m) 
             /\ ProcessMsg(m)  \* Generic action for handling a msg.
          \/ /\ ~ValidMsg(m)
             /\ DropMsg(m)

=============================================================================
\* Modification History
\* Last modified Thu May 14 10:58:32 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

