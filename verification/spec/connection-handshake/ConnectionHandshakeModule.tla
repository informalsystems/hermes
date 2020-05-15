--------------------- MODULE ConnectionHandshakeModule ---------------------

(***************************************************************************

    This module is part of the TLA+ specification for the
    IBC Connection Handshake protocol (ICS3).
    
    This module captures the actions and operators of the ICS3 protocol.
    Typically, it is an IBC module running on a chain that would implement
    the logic in this TLA+ module, hence the name "ConnectionHandshakeModule"
    sometimes abbreviated to "chModule" or "chm".

    This module deals with a high-level spec of the ICS3 protocol, so it is
    a simplification with respect to ICS3 proper in several regards:
    - the modules assumes to run on a chain which we model as a simple
    advancing height, plus a few more critical fields (see the 'store'),
    but without any state (e.g., blockchain, transactions, consensus core);
    - we model a single connection; establishing multiple connections is not
    possible;
    - we do not perform any cryptographic proofs or proof verifications.
    - the abstractions we use are higher-level, and slightly different from
    the ones in ICS3 (see e.g., ConnectionEnd and Connection records).
    - the client colocated with the module is simplified, comprising only
    a set of heights.

 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences


CONSTANTS MaxHeight,        \* Maximum height of the local chain.
          ConnectionIDs,    \* The set of valid connection IDs.
          ClientIDs,        \* The set of valid client IDs.
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


moduleVars == <<inBuf, outBuf, store>>


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


(* Modifies the local store.

    Replaces the connection in the store with the argument 'newCon'.
    If the height (latestHeight) of the chain has not yet attained MaxHeight, this action also
    advances the chain height. 
 *)
NewStore(newCon) ==
    [store EXCEPT !.connection = newCon,
                  !.latestHeight = @ + 1]


(* Handles a "ICS3MsgInit" message 'm'.
    
    Primes the store.connection to become initialized with the parameters
    specified in 'm'. Also creates a reply message, enqueued on the outgoing
    buffer.
 *)
HandleInitMsg(m) ==
    LET newCon == [parameters |-> m.parameters,
                   state      |-> "INIT"]
        sProof == GetConnProof("INIT")
        cProof == GetClientProof
        replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                     type |-> "ICS3MsgTry",
                     connProof |-> sProof,
                     clientProof |-> cProof] IN
    IF /\ ValidConnectionParameters(m.parameters)
       /\ store.connection.state = "UNINIT"
    THEN [out |-> Append(outBuf, replyMsg),
          store |-> NewStore(newCon)]
    ELSE [out |-> outBuf,
          store |-> store]


(* State predicate, guarding the handler for the Try msg.

    If any of these preconditions does not hold, the message
    is dropped. 
 *)
PreconditionsTryMsg(m) ==
    /\ ValidConnectionParameters(m.parameters)
    /\ \/ store.connection.state = "UNINIT"
       \/ /\ store.connection.state = "INIT"
          /\ CheckLocalParameters(m.parameters)
    /\ m.connProof.connectionState = "INIT"
    /\ VerifyConnProof(m.connProof)
    /\ VerifyClientProof(m.clientProof)


(* Handles a "ICS3MsgTry" message.
 *)
HandleTryMsg(m) ==
    LET newCon == [parameters |-> m.parameters, 
                   state |-> "TRYOPEN"]
        sProof == GetConnProof("TRYOPEN")
        cProof == GetClientProof
        replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                     type |-> "ICS3MsgAck",
                     connProof |-> sProof,
                     clientProof |-> cProof] IN
    IF PreconditionsTryMsg(m)
    THEN [out |-> Append(outBuf, replyMsg),
          store |-> NewStore(newCon)]
    ELSE [out |-> outBuf,
          store |-> store]


(* State predicate, guarding the handler for the Ack msg. 
 *)
PreconditionsAckMsg(m) ==
    /\ \/ store.connection.state = "INIT"
       \/ store.connection.state = "TRYOPEN"
    /\ CheckLocalParameters(m.parameters)
    /\ m.connProof.connectionState = "TRYOPEN"
    /\ VerifyConnProof(m.connProof)


(* Handles a "ICS3MsgAck" message.
 *)
HandleAckMsg(m) ==
    LET newCon == [parameters |-> m.parameters, 
                   state |-> "OPEN"]
        sProof == GetConnProof("OPEN")
        cProof == GetClientProof
        replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                     type |-> "ICS3MsgConfirm",
                     connProof |-> sProof,
                     clientProof |-> cProof] IN
    IF PreconditionsAckMsg(m)
    THEN [out |-> Append(outBuf, replyMsg),
          store |-> NewStore(newCon)]
    ELSE [out |-> outBuf,
          store |-> store]


(* State predicate, guarding the handler for the Confirm msg. 
 *)
PreconditionsConfirmMsg(m) ==
    /\ store.connection.state = "TRYOPEN"
    /\ CheckLocalParameters(m.parameters)
    /\ m.connProof.connectionState = "OPEN"
    /\ VerifyConnProof(m.connProof)

(* Handles a "ICS3MsgConfirm" message.
 *)
HandleConfirmMsg(m) ==
    LET newCon == [parameters |-> m.parameters,
                   state |-> "OPEN"] IN 
    IF PreconditionsConfirmMsg(m)
    THEN [out |-> outBuf,    (* Never need to reply to a confirm msg. *)
          store |-> NewStore(newCon)]
    ELSE [out |-> outBuf,
          store |-> store]


(* If MaxHeight is not yet reached, then advance the latestHeight of the chain.
 *) 
AdvanceChainHeight ==
    store' = [store EXCEPT !.latestHeight = @ + 1]


(* State predicate returning true if MaxHeight not yet attained.
 *)
CanProgress ==
    store.latestHeight < MaxHeight


(* Action for updating the local client on this chain with a new height.
    
    This may prime the store; leaves the chain buffers unchanged.
    This will also advance the chain height unless MaxHeight is reached.
    If the 'height' parameter already exists as part of
    'store.client.consensusStates', then we do not change the store.
 *)
UpdateClient(height) ==
    store' = [store EXCEPT !.latestHeight = @ + 1,
                           !.client.consensusStates = @ \cup {height},
                           !.client.latestHeight = height]


(* Generic action for handling any type of inbound message.

    Expects as parameter a message.
    Takes care of invoking priming the 'store' and any reply msg in 'outBuf'.
    This action assumes the message type is valid, therefore one of the
    disjunctions will always enable.
 *)
ProcessMsg(m) ==
    LET res == CASE m.type = "ICS3MsgInit" -> HandleInitMsg(m)
                 [] m.type = "ICS3MsgTry" -> HandleTryMsg(m)
                 [] m.type = "ICS3MsgAck" -> HandleAckMsg(m)
                 [] m.type = "ICS3MsgConfirm" -> HandleConfirmMsg(m) IN
    /\ outBuf' = res.out
    /\ store' = res.store


(***************************************************************************
 Connection Handshake Module (ICS3) main spec.
 ***************************************************************************)


Init(chainID, client) ==
    /\ store = [id |-> chainID,
                latestHeight |-> 1,
                connection |-> nullConnection,
                client |-> client]


Next ==
    \/ /\ inBuf # <<>>            \* Enabled if we have an inbound msg.
       /\ store.latestHeight < MaxHeight
       /\ ProcessMsg(Head(inBuf)) \* Generic action for handling a msg.
       /\ inBuf' = Tail(inBuf)    \* Strip the head of our inbound msg. buffer.
    \/ /\ inBuf = <<>>
       /\ store.latestHeight = MaxHeight
       /\ UNCHANGED<<moduleVars>>




=============================================================================
\* Modification History
\* Last modified Fri May 15 12:55:45 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

