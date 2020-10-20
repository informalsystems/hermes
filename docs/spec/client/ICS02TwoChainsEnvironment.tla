---------------------- MODULE ICS02TwoChainsEnvironment ----------------------

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          NrClientsChainA, \* number of clients that will be created on ChainA
          NrClientsChainB, \* number of clients that will be created on ChainA
          ClientIDsChainA, \* a set of counterparty client IDs for ChainA
          ClientIDsChainB \* a set of counterparty client IDs for ChainB

ASSUME MaxHeight < 10

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          datagramsChainA, \* set of datagrams incoming to ChainA
          datagramsChainB, \* set of datagrams incoming to ChainB
          history \* history variable

chainAvars == <<chainAstore, datagramsChainA>>
chainBvars == <<chainBstore, datagramsChainB>>
vars == <<chainAstore, datagramsChainA, 
          chainBstore, datagramsChainB, 
          history>>
          
(***************************************************************************
 Instances of ICS02Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE ICS02Chain
          WITH ChainID <- "chainA",
               NrClients <- NrClientsChainA,
               ClientIDs <- ClientIDsChainA,
               chainStore <- chainAstore,
               incomingDatagrams <- datagramsChainA

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE ICS02Chain
          WITH ChainID <- "chainB",
               NrClients <- NrClientsChainB,
               ClientIDs <- ClientIDsChainB,
               chainStore <- chainBstore,
               incomingDatagrams <- datagramsChainB
               
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore 
    <: ChainStoreType   
    
GetNrClientsByID(chainID) ==
    IF chainID = "chainA"
    THEN NrClientsChainA
    ELSE NrClientsChainB
             
       
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 
\* non-deterministically create datagrams
CreateDatagrams ==
    \* pick a sequence from the set of client datagrams non-deterministically
    \* for each chain     
    /\ datagramsChainA = AsSetDatagrams({})
    /\ datagramsChainB = AsSetDatagrams({})  
    /\ datagramsChainA' \in 
        SUBSET ClientDatagrams(
            ClientIDsChainA, 
            SetHeights(1, GetLatestHeight(GetChainByID("chainB")))
        )
    /\ datagramsChainB' \in
        SUBSET ClientDatagrams(
            ClientIDsChainB, 
            SetHeights(1, GetLatestHeight(GetChainByID("chainA")))
        )     
        
    /\ UNCHANGED <<chainAstore, chainBstore>>
    /\ UNCHANGED history        

    
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
    /\ history = [clientID \in (ClientIDsChainA \union ClientIDsChainB) |-> 
                    [created |-> FALSE, updated |-> FALSE]]   
    
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

ClientHeightsAreBelowCounterpartyHeight ==
    \A chainID \in ChainIDs :
        \A clientNr \in 1..GetNrClientsByID(chainID) :
            (GetChainByID(chainID).clientStates[clientNr].heights /= {} 
                => (Max(GetChainByID(chainID).clientStates[clientNr].heights) 
                     <= GetLatestHeight(GetChainByID(GetCounterpartyChainID(chainID)))))

Inv ==
    /\ ChainA!CreatedClientsHaveDifferentIDs
    /\ ChainA!UpdatedClientsAreCreated
    /\ ChainB!CreatedClientsHaveDifferentIDs
    /\ ChainB!UpdatedClientsAreCreated  
    /\ ClientHeightsAreBelowCounterpartyHeight
    
      
        
=============================================================================
\* Modification History
\* Last modified Mon Oct 19 18:34:24 CEST 2020 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
