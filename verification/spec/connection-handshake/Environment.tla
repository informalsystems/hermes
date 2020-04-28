---------------------------- MODULE Environment ----------------------------

EXTENDS Naturals, FiniteSets


CONSTANT MaxHeight     \* Maximum height of any chain in the system.


VARIABLES
    turn,
    msgToA,
    msgToB,
    chainAStore,
    chainBStore


vars == <<turn, msgToA, msgToB, chainAStore, chainBStore>>


chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight  <- MaxHeight,
             inMsg      <- msgToA,
             outMsg     <- msgToB,
             store      <- chainAStore


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxHeight  <- MaxHeight,
             inMsg      <- msgToB,      \* Flip the message buffers w.r.t. chain A buffers.
             outMsg     <- msgToA,       \* Inbound for "A" is outbound for "B".
             store      <- chainBStore


(***************************************************************************
 Environment actions.
 ***************************************************************************)

InitEnv ==
    /\ msgToA = chmA!noMsg
    /\ msgToB = chmB!noMsg


NextEnv ==
    \/ /\ msgToA' \in chmA!ConnectionHandshakeMessages
       /\ UNCHANGED msgToB 
    \/ /\ msgToB' \in chmB!ConnectionHandshakeMessages
       /\ UNCHANGED msgToA


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
    /\ FlipTurn
    /\ IF turn = "env"
        THEN /\ NextEnv
             /\ UNCHANGED <<chainAStore, chainBStore>>
        ELSE IF turn = "chmA"
                THEN /\ chmA!Next
                     /\ UNCHANGED chainBStore
                ELSE /\ chmB!Next
                     /\ UNCHANGED chainAStore
     \* Handle the exceptional case when turn is neither of chm or env?


Spec ==
    /\ Init
    /\ [][Next]_<<vars>>
    /\ WF_turn(FlipTurn)


TypeInvariant ==
    /\ turn \in {"env", "chmA", "chmB"}
    /\ msgToA \in chmA!ConnectionHandshakeMessages
    /\ msgToB \in chmB!ConnectionHandshakeMessages


\* Model check it!
THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Tue Apr 28 16:41:12 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

