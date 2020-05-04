---------------------------- MODULE Environment ----------------------------

EXTENDS Naturals, FiniteSets


CONSTANT MaxHeight     \* Maximum height of any chain in the system.


VARIABLES
    bufChainA,      \* A buffer for messages inbound to chain A.
    bufChainB,
    storeChainA,    \* The local store of chain A.
    storeChainB,
    stillMalicious


chainAVars == <<bufChainA, bufChainB, storeChainA>>
chainBVars == <<bufChainA, bufChainB, storeChainB>>
chainVars == <<bufChainA, bufChainB, storeChainA, storeChainB>>
allVars == <<chainVars, stillMalicious>>


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
    /\ stillMalicious = TRUE
    /\ \/ bufChainA = chmA!InitMsg \* chmA!noMsg
       \/ bufChainB = chmB!InitMsg \* chmB!noMsg


MaliciousNextEnv ==
    \/ /\ bufChainA' \in chmA!ConnectionHandshakeMessages
       /\ UNCHANGED bufChainB 
    \/ /\ bufChainB' \in chmB!ConnectionHandshakeMessages
       /\ UNCHANGED bufChainA


(* TODO: Eventually, it should be just 'good'. *)
NextEnv ==
    \/ stillMalicious /\ MaliciousNextEnv /\ UNCHANGED stillMalicious
    \/ stillMalicious /\ stillMalicious' = FALSE
    

CHDone ==
    /\ storeChainA.connection.state = "OPEN" 
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED <<allVars>>

(******************************************************************************
 Main spec.
 The system comprises the connection handshake module & environment.
 *****************************************************************************)


Init ==
    /\ InitEnv
    /\ chmA!Init("chainA")
    /\ chmB!Init("chainB")


\* The two CH modules and the environment alternate their steps.
Next ==
    \/ CHDone
    \/ NextEnv /\ UNCHANGED <<chainVars>>
    \/ chmA!Next /\ UNCHANGED storeChainB
    \/ chmB!Next /\ UNCHANGED storeChainA


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)


TypeInvariant ==
    /\ bufChainA \in chmA!ConnectionHandshakeMessages
    /\ bufChainB \in chmB!ConnectionHandshakeMessages


\* Liveness property.
Termination ==
    <> ~ stillMalicious
        => <> /\ storeChainA.connection.state = "INIT" (* should be OPEN *)
              /\ storeChainB.connection.state = "INIT"


\* Safety property.
\* If the connections in the two chains are not null, then the
\* connection parameters must always match.
ConsistencyInv ==
    \/ storeChainA.connection = chmA!nullConnection
    \/ storeChainB.connection = chmB!nullConnection
    \/ storeChainA.connection.parameters 
        = chmB!FlipConnectionParameters(storeChainB.connection.parameters)

Consistency ==
    [] ConsistencyInv

=============================================================================
\* Modification History
\* Last modified Mon May 04 14:56:16 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

