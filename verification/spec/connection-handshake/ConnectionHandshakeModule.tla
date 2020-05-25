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

    - we do not perform any cryptographic proof verifications;

    - the abstractions we use are higher-level, and slightly different from
    the ones in ICS3 (see e.g., ConnectionEnd and Connection records).

    - the client colocated with the module is simplified, comprising only
    a set of heights (not the actual blockchain headers).

 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, ICS3Types


CONSTANTS MaxChainHeight,   \* Maximum height of the local chain.
          ConnectionIDs,    \* The set of valid connection IDs.
          ClientIDs,        \* The set of valid client IDs.
          MaxBufLen         \* Maximum length of the input and output buffers.


ASSUME Cardinality(ConnectionIDs) >= 1
ASSUME Cardinality(ClientIDs) >= 1


VARIABLES
(******************************* Store *****************************

     The store record of a chain contains the following fields:

     - chainID -- a string 
       Stores the identifier of the chain where this module executes.

     - latestHeight -- a natural number in the range 1..MaxHeight
       Describes the current height of the chain.  

     - connection -- a connection record.
       Captures all the details of the connection on this chain.
       For a full description of a connection record, see the
       'Environment.Connections' set.

     - client -- a client record.
       Specifies the state of the client running on this chain.

       A client record contains the following fields:

         - consensusHeights -- a set of heights 
           Stores the set of all heights (i.e., consensus states) that this
           client observed.

         - clientID -- a string
           The identifier of the client.

         - latestHeight -- a natural number in the range 1..MaxHeight
           Stores the latest height among all the heights in consensusHeights.

        For more details on how clients are initialized, see the operator
        ICS3Types.InitClients. 

 ***************************************************************************)
    store,
    (* A buffer (Sequence) holding any message(s) incoming to this module. *)
    inBuf,
    (* A buffer (Sequence) holding outbound message(s) from this module. *)
    outBuf


moduleVars ==
    <<inBuf, outBuf, store>>


(***************************************************************************
    Helper operators.
 ***************************************************************************)


(* Simple computation returning the maximum out of two numbers 'a' and 'b'.
 *)
MAX(a, b) ==
    IF a > b THEN a ELSE b


(* Validates a connection parameter.

    Returns true if 'para' matches the parameters in the local connection,
    and returns false otherwise.

 *)
ValidConnectionParameters(para) ==
    LET local == store.connection.parameters.localEnd
        remote == store.connection.parameters.remoteEnd 
    IN /\ local.connectionID = para.localEnd.connectionID   
       /\ remote.connectionID = para.remoteEnd.connectionID
       /\ local.clientID = para.localEnd.clientID       
       /\ remote.clientID = para.remoteEnd.clientID


(* Validates a connection parameter local end.

    Expects as input a ConnectionParameter 'para' and returns true or false.
    This is a basic validation step, making sure that the local end in 'para'
    is valid with respect to module-level constants ConnectionIDs and ClientIDs.

*)
ValidLocalEnd(para) ==
    /\ para.localEnd.connectionID \in ConnectionIDs
    /\ para.localEnd.clientID \in ClientIDs


(* Operator for reversing the connection ends.

    Given a ConnectionParameters record 'para', returns a new set
    of parameters where the local and remote ends are
    flipped (i.e., reversed).
 *)
FlipConnectionParameters(para) ==
    [localEnd   |-> para.remoteEnd,
     remoteEnd  |-> para.localEnd]


(* Operator for constructing a connection proof.

    The connection proof is used to demonstrate to another chain that the
    local store on this chain comprises a connection in a certain state. 
 *)
GetConnProof(myConnection) ==
    [connection |-> myConnection]


(* Operator for constructing a client proof.
 *)
GetClientProof ==
    [latestHeight |-> store.client.latestHeight,
     consensusHeights |-> store.client.consensusHeights]


(* Verification of a connection proof. 

    This is a state predicate returning true if the following holds: 
    - the state of connection in this proof should match with input parameter
    'expectedState'; and
    - the connection parameters in this proof should match with the flipped version
    of the input 'expectedParams'.

 *)
VerifyConnProof(cp, expectedState, expectedParams) ==
    /\ cp.connection.state = expectedState
    /\ cp.connection.parameters = FlipConnectionParameters(expectedParams)


(* Verification of a client proof.

    This is a state predicate returning true if the following holds: the height
    reported in the client proof must not exceed the current (latestHeight) of
    this chain.
 *)
VerifyClientProof(cp) ==
    /\ cp.latestHeight <= store.latestHeight   (* Consistency height check. *)
    /\ cp.latestHeight \in cp.consensusHeights (* Client verification step. *)


(***************************************************************************
 Connection Handshake Module actions & operators.
 ***************************************************************************)


(* Modifies the local store.

    Replaces the connection in the store with the argument 'newCon'.
    This action also advances the chain height. 
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
        myConnProof == GetConnProof(newCon)
        myClientProof == GetClientProof
        replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                     type |-> "ICS3MsgTry",
                     proofHeight |-> store.latestHeight,
                     connProof |-> myConnProof,
                     clientProof |-> myClientProof] IN
    IF /\ ValidLocalEnd(m.parameters)  (* Basic validation of localEnd in parameters. *)
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
    /\ \/ /\ store.connection.state = "UNINIT"
          /\ ValidLocalEnd(m.parameters)
       \/ /\ store.connection.state = "INIT"
          /\ ValidConnectionParameters(m.parameters)
    /\ m.proofHeight \in store.client.consensusHeights (* Consistency height check. *)
    /\ VerifyConnProof(m.connProof, "INIT", m.parameters)
    /\ VerifyClientProof(m.clientProof)


(* Handles a "ICS3MsgTry" message.
 *)
HandleTryMsg(m) ==
    LET newCon == [parameters |-> m.parameters, 
                   state |-> "TRYOPEN"]
        myConnProof == GetConnProof(newCon)
        myClientProof == GetClientProof
        replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                     type |-> "ICS3MsgAck",
                     proofHeight |-> store.latestHeight,
                     connProof |-> myConnProof,
                     clientProof |-> myClientProof] IN
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
    /\ ValidConnectionParameters(m.parameters)
    /\ m.proofHeight \in store.client.consensusHeights (* Consistency height check. *)
    /\ VerifyConnProof(m.connProof, "TRYOPEN", m.parameters)
    /\ VerifyClientProof(m.clientProof)


(* Handles a "ICS3MsgAck" message.
 *)
HandleAckMsg(m) ==
    LET newCon == [parameters |-> m.parameters, 
                   state |-> "OPEN"]
        myConnProof == GetConnProof(newCon)
        replyMsg == [parameters |-> FlipConnectionParameters(m.parameters),
                     proofHeight |-> store.latestHeight,
                     type |-> "ICS3MsgConfirm",
                     connProof |-> myConnProof] IN
    IF PreconditionsAckMsg(m)
    THEN [out |-> Append(outBuf, replyMsg),
          store |-> NewStore(newCon)]
    ELSE [out |-> outBuf,
          store |-> store]


(* State predicate, guarding the handler for the Confirm msg. 
 *)
PreconditionsConfirmMsg(m) ==
    /\ store.connection.state = "TRYOPEN"
    /\ ValidConnectionParameters(m.parameters)
    /\ m.proofHeight \in store.client.consensusHeights (* Consistency height check. *)
    /\ VerifyConnProof(m.connProof, "OPEN", m.parameters)


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


(* Action for advancing the current height (latestHeight) of the chain.

    The environment triggers this as part of the GoodNextEnv action.
 *) 
AdvanceChainHeight ==
    store' = [store EXCEPT !.latestHeight = @ + 1]


(* State predicate returning true if MaxChainHeight not yet attained.
 *)
CanAdvance ==
    store.latestHeight < MaxChainHeight


(* Action for updating the local client on this chain with a new height.

    This primes the store; leaves the chain buffers unchanged.
    This will also advance the chain height.
 *)
UpdateClient(height) == 
    /\ store' = [store EXCEPT !.latestHeight = @ + 1,
                              !.client.consensusHeights = @ \cup {height},
                              !.client.latestHeight = MAX(height, store.client.latestHeight)]

CanUpdateClient(height) ==
    /\ CanAdvance
    /\ height \notin store.client.consensusHeights
    

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
    /\ store = [chainID |-> chainID,
                latestHeight |-> 1,
                connection |-> NullConnection,
                client |-> client]


Next ==
    \/ /\ inBuf # <<>>            \* Enabled if we have an inbound msg.
       /\ CanAdvance
       /\ ProcessMsg(Head(inBuf)) \* Generic action for handling a msg.
       /\ inBuf' = Tail(inBuf)    \* Strip the head of our inbound msg. buffer.
    \/ /\ inBuf = <<>>
       /\ ~ CanAdvance
       /\ UNCHANGED<<moduleVars>>


TypeInvariant ==
    /\ inBuf \in Seq(ConnectionHandshakeMessages) \union {<<>>}
    /\ outBuf \in Seq(ConnectionHandshakeMessages) \union {<<>>} 
    /\ store \in Stores


=============================================================================
\* Modification History
\* Last modified Thu May 21 09:22:33 CEST 2020 by adi
\* Created Fri Apr 24 19:08:19 CEST 2020 by adi

