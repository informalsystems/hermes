--------------------------------- MODULE CH ---------------------------------

EXTENDS Naturals, FiniteSets


CONSTANT MaxHeight     \* Maximum height of all the chains in the system.


VARIABLES
    chModule,   \* The state of this connection handshake module (chm).
    turn,       \* Keep track of who takes a step: either chModule or environment.
    inMsg,      \* A buffer holding any message incoming to the chModule.
    outMsg      \* A buffer holding any message outbound from the chModule.


vars == <<turn, chModule, inMsg, outMsg>>

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

    - connectionID -- a connection identifier
      Stores the connection identifier for this connection end.

    - clientID -- a client identifier
      Stores the client identifier associated with this connection end.

    Optional, add later:
    - prefix
    
 ***************************************************************************)
ConnectionEnds ==
    [
        connectionID : ConnectionIDs \union {Null},
        clientID : ClientIDs \union {Null}
    ]


(***************************** Connections *****************************
    A set of connection records.
    A connection record contains the following fields:

    - localEnd -- a connection end
      Stores the connection end for the local chain.

    - remoteEnd -- a connection end
      Stores the connection end for the remote chain.
 ***************************************************************************)
Connections ==
    [
        localEnd : ConnectionEnds,
        remoteEnd : ConnectionEnds
    ]


(***************************** ConnectionHandshakeModules ******************
    A set of records defining the CHM.
    A CHM record contains the following fields:

    - connectionState -- a string
      Stores the current state of this connection. It has one of the
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".

    - connection -- a connection with two ends
      Stores the connection.

    - chainHeight -- a height
      Stores the height of the chain running alongside the CHM.
 ***************************************************************************)
ConnectionHandshakeModules ==
    [
        connectionState : ConnectionStates,
        connection : Connections,
        chainHeight : Heights
        \* light client, consensus state, etc.. 
    ]



(******************************** Messages ********************************
These messages are connection handshake specific.
 ***************************************************************************)
ConnectionHandshakeMessages ==
    [type : {"ConnOpenInit"}, 
     connection : Connections]
\*    \union
\*    [type : {"ConnOpenTry"},
\*        connection : Connections,
\*        stateProof : Proofs, 
\*        consensusHeight : Proofs]



(***************************************************************************
 Connection handshake message handlers.
***************************************************************************)

\* The chModule handles a "ConnOpenInit" message.
connectionOpenInit(chm, initMsg) ==
  \* If we're in the right state.
  IF chm.connectionState = "UNINIT" THEN
         [initCHM |-> [chm EXCEPT !.connection = initMsg.connection,
                                  !.connectionState = "INIT"],
          msg |-> [type |-> "ConnOpenTry",
                   connection |-> initMsg.connection]]
                   \* TODO: Proofs go here.                   
   \* Otherwise, do not update the chain
   ELSE [initCHM |-> chm,
         msg |-> noMsg ]

handleMsgConnectionOpenInit ==
 /\ inMsg.type = "ConnOpenInit"
 /\ LET res == connectionOpenInit(chModule, inMsg) IN
      /\ chModule' = res.initCHM
      /\ outMsg' = res.msg
      /\ UNCHANGED <<inMsg>>



(***************************************************************************
 Connection Handshake Module actions.
 ***************************************************************************)

\* Advance the height of the chain if MaxHeight is not yet reached.
advanceChain ==
    /\ chModule.chainHeight < MaxHeight
    /\ chModule' = [chModule EXCEPT
                    !.chainHeight = chModule.chainHeight + 1
                 ]
    /\ UNCHANGED <<outMsg, inMsg>>


(***
  * Initial value for a connection end.
  **)
ConnectionEndInitValue ==
    [connectionID |-> Null,
     clientID |-> Null]


(***
  * Initial values for a connection.
  **)
ConnectionInitValue ==
    [localEnd |-> ConnectionEndInitValue,
     remoteEnd |-> ConnectionEndInitValue]

CHModuleInitValue ==
    [chainHeight |-> 1,
     connectionState |-> "UNINT",
     connection |-> ConnectionInitValue ]

InitCHModule ==
    /\ chModule = CHModuleInitValue
    /\ outMsg = noMsg

NextCHModule ==
    \/ advanceChain
    \/ handleMsgConnectionOpenInit

(***************************************************************************
 Environment actions
 ***************************************************************************)

 InitEnv ==
   /\ inMsg = noMsg

 OnConnInitMsg ==
   /\ inMsg' \in [type: {"ConnOpenInit"},
                  connection : Connections]

 NextEnv ==
     \/ OnConnInitMsg


(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)

Init ==
    turn = "env" \* Initially, the environment takes a turn.
    /\ InitEnv
    /\ InitCHModule


\* Turn-flipping mechanism.
FlipTurn ==
  turn' = (
    IF turn = "chm" THEN
      "env"
    ELSE
      "chm"
  )


\* chModule and environment alternate their steps
Next ==
/\ FlipTurn
/\ IF turn = "chm" THEN
     /\ NextCHModule
     /\ inMsg' = noMsg
   ELSE
     /\ NextEnv
     /\ outMsg' = noMsg
     /\ UNCHANGED chModule
     \* Handle the exceptional case when turn is neither of chm or env?

Spec ==
    Init
    /\ [][Next]_<<vars>>
    /\ WF_turn(FlipTurn)


TypeInvariant ==
    /\ inMsg \in ConnectionHandshakeMessages \union { noMsg }


\* Model check it!
THEOREM Spec => []TypeInvariant


=============================================================================
\* Modification History
\* Last modified Wed Apr 22 17:43:57 CEST 2020 by adi
\* Wed Apr 22 10:42:14 CEST 2020 improvements & suggestions by anca & zarko
\* Created Fri Apr 17 10:28:22 CEST 2020 by adi


