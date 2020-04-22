--------------------------------- MODULE CH ---------------------------------

EXTENDS Naturals, FiniteSets


CONSTANT MaxHeight     \* Maximum height of all the chains in the system.


VARIABLES
    turn,    \* Keep track of who takes a step: either connection module or environment.
    chain,   \* The state of this (local) chain.
    inMsg,   \* A buffer holding any message incoming to the chain.
    outMsg   \* A buffer holding any message outbound from the chain.


vars == <<turn, chain, inMsg, outMsg>>

Heights == 1..MaxHeight

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

ConnectionIDs == {"connAtoB", "connBtoA"}
ClientIDs == { "clientA", "clientB" }

Null == "none"
noMsg == [ type |-> "none" ]
noErr == "errNone"


(***************************** ConnectionEnds *****************************
    A set of connection end records.
    A connection end record contains the following fields:

    - state -- a string
      Stores the current state of this connection end. It has one of the
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".

    - connectionID -- a connection identifier
      Stores the connection identifier of this connection end.

    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the counterparty connection end.

    - clientID -- a client identifier
      Stores the client identifier associated with this connection end.

    - counterpartyClientID -- a client identifier
      Stores the counterparty client identifier associated with this connection end.
 ***************************************************************************)
ConnectionEnds ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {Null},
        clientID : ClientIDs \union {Null},
        counterpartyConnectionID : ConnectionIDs \union {Null},
        counterpartyClientID : ClientIDs \union {Null}
    ]

(******************************** Datagrams ********************************
Specify the connection-handshake specific datagrams.
TODO: Unclear if we should insist on calling these 'datagrams' or more
generally just 'messages' (@Zarko).

TODO: @Zarko: In my view this abstraction should be called ConnectionEnd
and what is currently called ConnectionEnd should be Connection.
 ***************************************************************************)
ConnectionDatagrams ==
    [type : {"ConnOpenInit"}, connectionID : ConnectionIDs, clientID : ClientIDs,
     counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs]
    \union
    [type : {"ConnOpenTry"}, desiredConnectionID : ConnectionIDs,
     counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs,
     clientID : ClientIDs, proofHeight : Heights, consensusHeight : Heights]



(***************************************************************************
Connection datagram handlers
***************************************************************************)

\* Handle "ConnOpenInit" datagrams
connectionOpenInit(ch, datagram) ==
  IF ch.connectionEnd.state = "UNINIT" THEN
       LET connOpenInitConnectionEnd == [
           state |-> "INIT",
           connectionID |-> datagram.connectionID,
           clientID |-> datagram.clientID,
           counterpartyConnectionID |-> datagram.counterpartyConnectionID,
           counterpartyClientID |-> datagram.counterpartyClientID]
       IN
       [ chain |-> [ch EXCEPT !.connectionEnd = connOpenInitConnectionEnd],
         msg |-> [
           type |-> "ConnOpenTry",
           connectionID |-> connOpenInitConnectionEnd.counterpartyConnectionID,
           clientID |-> connOpenInitConnectionEnd.counterpartyClientID,
           counterpartyConnectionID |-> connOpenInitConnectionEnd.connectionID,
           counterpartyClientID |-> connOpenInitConnectionEnd.clientID ] ]
   \* otherwise, do not update the chain
   ELSE [  chain |-> ch,
           msg |-> noMsg ]

handleMsgConnectionOpenInit ==
 /\ inMsg.type = "ConnOpenInit"
 /\ LET res == connectionOpenInit(chain, inMsg) IN
      /\ chain' = res.chain
      /\ outMsg' = res.msg



(***************************************************************************
 Chain actions
 ***************************************************************************)

\* Advance the height of the chain until MaxHeight is reached
advanceChain ==
    /\ chain.height < MaxHeight
    /\ chain' = [chain EXCEPT
                    !.height = chain.height + 1
                 ]
    /\ UNCHANGED outMsg

(***
  * Initial values for the chain.
  **)
InitConnectionEnd ==
    [state |-> "UNINIT",
     connectionID |-> Null,
     clientID |-> Null,
     counterpartyConnectionID |-> Null,
     counterpartyClientID |-> Null]

InitChain ==
    [height |-> 1,
     connectionEnd |-> InitConnectionEnd]

InitCh ==
    /\ chain = InitChain
    /\ outMsg = noMsg

NextCh ==
    \/ advanceChain
    \/ handleMsgConnectionOpenInit

(***************************************************************************
 Environment actions
 ***************************************************************************)

 InitEnv ==
   /\ inMsg = noMsg

 OnConnInitMsg ==
   /\ inMsg' \in [type: {"ConnOpenInit"},
                  connectionID : ConnectionIDs,
                  clientID : ClientIDs,
                  counterpartyConnectionID : ConnectionIDs,
                  counterpartyClientID : ClientIDs]

 NextEnv ==
     \/ OnConnInitMsg


(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)

Init ==
    turn = "env" \* Initially, the environment takes a turn.
    /\ InitEnv
    /\ InitCh

\* Turn-flipping mechanism.
FlipTurn ==
  turn' = (
    IF turn = "ch" THEN
      "env"
    ELSE
      "ch"
  )

\* chModule and environment alternate their steps
Next ==
/\ FlipTurn
/\ IF turn = "ch" THEN
     /\ NextCh
     /\ inMsg' = noMsg
   ELSE
     /\ NextEnv
     /\ outMsg' = noMsg
     /\ UNCHANGED chain
     \* Handle the exceptional case when turn is neither of ch or env?

Spec ==
    Init
    /\ [][Next]_<<vars>>
    /\ WF_turn(FlipTurn)


TypeInvariant ==
    /\ inMsg \in ConnectionDatagrams


\* Model check it!
THEOREM Spec => []TypeInvariant


=============================================================================
\* Modification History
\* Last modified Wed Apr 22 16:19:44 CEST 2020 by adi
\* Wed Apr 22 10:42:14 CEST 2020 improvements & suggestions by anca & zarko
\* Created Fri Apr 17 10:28:22 CEST 2020 by adi

