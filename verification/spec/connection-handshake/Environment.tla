---------------------------- MODULE Environment ----------------------------

EXTENDS Naturals, FiniteSets


CONSTANT MaxHeight     \* Maximum height of any chain in the system.


VARIABLES
    turn,
    bufChainA,      \* A buffer for messages inbound to chain A.
    bufChainB,
    storeChainA,    \* The local store of chain A.
    storeChainB


vars == <<turn, bufChainA, bufChainB, storeChainA, storeChainB>>


chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight  <- MaxHeight,
             inMsg      <- bufChainA,
             outMsg     <- bufChainB,
             store      <- storeChainA


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight  <- MaxHeight,
             inMsg      <- bufChainB,      \* Flip the message buffers w.r.t. chain A buffers.
             outMsg     <- bufChainA,      \* Inbound for "A" is outbound for "B".
             store      <- storeChainB


(***************************************************************************
 Environment actions.
 ***************************************************************************)


InitEnv ==
    /\ bufChainA = chmA!noMsg
    /\ bufChainB = chmB!noMsg


GoodNextEnv ==
    UNCHANGED <<bufChainA, bufChainB>>


MaliciousNextEnv ==
    \/ /\ bufChainA' \in chmA!ConnectionHandshakeMessages
       /\ UNCHANGED bufChainB 
    \/ /\ bufChainB' \in chmB!ConnectionHandshakeMessages
       /\ UNCHANGED bufChainA


(* TODO: Eventually, it should be just 'good'. *)
NextEnv ==
    \/ GoodNextEnv
    \/ MaliciousNextEnv


(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)

\* Turn-flipping mechanism.
\* This mechanism ensures that the turn goes round-robin the following order:
\* env -> chmA -> chmB -> env -> ...
FlipTurn ==
    turn' = (
        IF turn = "chmA"
            THEN "chmB"             \* After A goes B.
            ELSE IF turn = "chmB"
                    THEN "env"      \* After B goes the environment.
                    ELSE "chmA"     \* After env goes A.
    )


Init ==
    /\ turn = "env" \* Initially, the environment takes a turn.
    /\ InitEnv
    /\ chmA!Init("chainA")
    /\ chmB!Init("chainB")


\* The two CH modules and the environment alternate their steps.
Next ==
    IF storeChainA.connection.state = "OPEN" /\ storeChainB.connection.state = "OPEN"
    THEN UNCHANGED <<vars>> 
    ELSE /\ FlipTurn
         /\ IF turn = "env"
            THEN /\ NextEnv
                 /\ UNCHANGED <<storeChainA, storeChainB>>
            ELSE IF turn = "chmA"
                 THEN /\ chmA!Next
                      /\ UNCHANGED storeChainB
                 ELSE /\ chmB!Next
                      /\ UNCHANGED storeChainA


Spec ==
    /\ Init
    /\ [][Next]_<<vars>>
    /\ WF_turn(FlipTurn)


TypeInvariant ==
    /\ turn \in {"env", "chmA", "chmB"}
    /\ bufChainA \in chmA!ConnectionHandshakeMessages
    /\ bufChainB \in chmB!ConnectionHandshakeMessages


\* Model check it!
THEOREM Spec => []TypeInvariant


\* Liveness property.
Termination ==
    <> /\ storeChainA.connection.state = "INIT"
       /\ storeChainA.connection.state = "INIT"


\* Safety property.
\* If the connections in the two chains are not null, then the
\* connection parameters must always match.
(* TODO: This should be incorporated in the THEOREM block. 
   Remove the box [] from this expression and do a conjuct w/ TypeInvariant:
        THEOREM Spec => [](TypeInvarianta /\ Consistency)
   See §5.7 of Lamport's SS book. *)
Consistency ==
    /\ storeChainA.connection /= chmA!nullConnection
    /\ storeChainB.connection /= chmB!nullConnection 
    => [] (storeChainA.connection.parameters 
            = chmB!FlipConnectionParameters(storeChainB.connection.parameters))
     

=============================================================================
\* Modification History
\* Last modified Fri May 01 15:45:17 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

