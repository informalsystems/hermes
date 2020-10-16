---------------------- MODULE ICS02TwoChainsEnvironment ----------------------

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS MaxHeight \* maximal height of all the chains in the system

ASSUME MaxHeight < 10

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          datagramsChainA, \* set of datagrams incoming to ChainA
          datagramsChainB, \* set of datagrams incoming to ChainB
          clientCreatedHistoryChainA, \* history variable for ChainA
          clientUpdatedHistoryChainA, \* history variable for ChainA
          clientCreatedHistoryChainB, \* history variable for ChainB
          clientUpdatedHistoryChainB \* history variable for ChainB

chainAvars == <<chainAstore, datagramsChainA, clientCreatedHistoryChainA, clientUpdatedHistoryChainA>>
chainBvars == <<chainBstore, datagramsChainB, clientCreatedHistoryChainB, clientUpdatedHistoryChainB>>
vars == <<chainAstore, datagramsChainA, clientCreatedHistoryChainA, clientUpdatedHistoryChainA,
          chainBstore, datagramsChainB, clientCreatedHistoryChainB, clientUpdatedHistoryChainB>>
          
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

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE ICS02Chain
          WITH ChainID <- "chainB",
               chainStore <- chainBstore,
               incomingDatagrams <- datagramsChainB,
               clientCreatedHistory <- clientCreatedHistoryChainB,
               clientUpdatedHistory <- clientUpdatedHistoryChainB        
               
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore 
    <: ChainStoreType        
       
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 
\* non-deterministically create datagrams
CreateDatagrams ==
    \* pick a sequence from the set of client datagrams non-deterministically
    \* for each chain     
    /\ datagramsChainA' \in 
        SUBSET ClientDatagrams(
            GetCounterpartyClientIDs("chainA"), 
            SetHeights(1, GetLatestHeight(GetChainByID("chainB")))
        )
    /\ datagramsChainB' \in
        SUBSET ClientDatagrams(
            GetCounterpartyClientIDs("chainB"), 
            SetHeights(1, GetLatestHeight(GetChainByID("chainB")))
        )     
        
    /\ UNCHANGED <<chainAstore, chainBstore>>
    /\ UNCHANGED <<clientCreatedHistoryChainA, clientUpdatedHistoryChainA>>
    /\ UNCHANGED <<clientCreatedHistoryChainB, clientUpdatedHistoryChainB>>        

    
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchanged       
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars

\* EnvironmentAction: non-deterministically create datagrams       
EnvironmentAction ==
    CreateDatagrams
    
(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init    
    
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
    /\ ChainB!CreatedClientsHaveDifferentIDs
    /\ ChainB!UpdatedClientsAreCreated    
        
=============================================================================
\* Modification History
\* Last modified Fri Oct 16 11:10:43 CEST 2020 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
