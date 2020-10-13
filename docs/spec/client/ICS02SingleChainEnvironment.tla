-------------------- MODULE ICS02SingleChainEnvironment --------------------

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS MaxHeight \* maximal height of all the chains in the system

ASSUME MaxHeight < 10

VARIABLES chainAstore, \* store of ChainA
          datagramsChainA, \* set of datagrams incoming to ChainA
          clientCreatedHistoryChainA, \* history variable
          clientUpdatedHistoryChainA \* history variable

chainAvars == <<chainAstore, datagramsChainA, clientCreatedHistoryChainA, clientUpdatedHistoryChainA>>
vars == <<chainAstore, datagramsChainA, clientCreatedHistoryChainA, clientUpdatedHistoryChainA>>
          
(***************************************************************************
 Instances of ICS02Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE ICS02Chain
          WITH ChainID <- "chainA",
               chainStore <- chainAstore,
               incomingDatagrams <- datagramsChainA,
               clientCreatedHistory <- clientCreatedHistoryChainA,
               clientUpdatedHistory <- clientUpdatedHistoryChainA          
       
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 
\* non-deterministically create datagrams
CreateDatagrams ==
    \* pick a sequence from the set of client datagrams non-deterministically
    /\ datagramsChainA' \in 
        SUBSET ClientDatagrams(
            GetCounterpartyClientIDs("chainA"), 
            1..MaxHeight
        )  
        
    /\ UNCHANGED <<chainAstore, clientCreatedHistoryChainA, clientUpdatedHistoryChainA>>

    
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: the chain takes a step
ChainAction ==
    ChainA!Next

\* EnvironmentAction: non-deterministically create datagrams       
EnvironmentAction ==
    CreateDatagrams
    
(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
Init ==
    /\ ChainA!Init
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars    
    
\* Specification formula
Spec == Init /\ [][Next]_vars    

(***************************************************************************
 Invariants
 ***************************************************************************)

Inv ==
    /\ ChainA!CreatedClientsHaveDifferentIDs
    /\ ChainA!UpdatedClientsAreCreated
    
=============================================================================
\* Modification History
\* Last modified Tue Oct 13 14:02:20 CEST 2020 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
