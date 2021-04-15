---------------------- MODULE ICS02TwoChainsEnvironment ----------------------

(***************************************************************************
 A TLA+ specification of the IBC client protocol (ICS02). This module models 
 a system consisting of two chain that can create multiple clients, and which 
 operate in an environment that overapproximates the behavior of a correct 
 relayer.    
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS 
    \* @type: Int;
    MaxHeight, \* maximal height of all the chains in the system
    \* @type: Int;
    NrClientsChainA, \* number of clients that will be created on ChainA
    \* @type: Int;
    NrClientsChainB, \* number of clients that will be created on ChainB
    \* @type: Set(Str);
    ClientIDsChainA, \* a set of counterparty client IDs for ChainA
    \* @type: Set(Str);
    ClientIDsChainB \* a set of counterparty client IDs for ChainB

ASSUME MaxHeight < 10
ASSUME ClientIDsChainA \intersect ClientIDsChainB = {}

VARIABLES 
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: CHAINSTORE;
    chainBstore, \* store of ChainB
    \* @type: Set(DATAGRAM);
    datagramsChainA, \* set of datagrams incoming to ChainA
    \* @type: Set(DATAGRAM);
    datagramsChainB, \* set of datagrams incoming to ChainB
    \* @type: Str -> [created: Bool, updated: Bool];
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
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               NrClients <- NrClientsChainA,
               ClientIDs <- ClientIDsChainA,
               chainStore <- chainAstore,
               incomingDatagrams <- datagramsChainA

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               NrClients <- NrClientsChainB,
               ClientIDs <- ClientIDsChainB,
               chainStore <- chainBstore,
               incomingDatagrams <- datagramsChainB
               
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore 
    
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
    /\ datagramsChainA = {}
    /\ datagramsChainB = {}
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

\* type invariant
TypeOK ==
    /\ ChainA!TypeOK
    /\ ChainB!TypeOK
    /\ history \in [ClientIDsChainA -> [created : BOOLEAN, updated : BOOLEAN]]

\* the maximum client height is less than or equal to the current height of 
\* the counterparty chain 
ClientHeightsAreBelowCounterpartyHeight ==
    \A chainID \in ChainIDs :
        \A clientNr \in 1..GetNrClientsByID(chainID) :
            (GetChainByID(chainID).clientStates[clientNr].heights /= {}
                => (Max(GetChainByID(chainID).clientStates[clientNr].heights) 
                     <= GetLatestHeight(GetChainByID(GetCounterpartyChainID(chainID)))))

\* conjunction of invariants
ICS02TwoChainsInv ==
    /\ ChainA!CreatedClientsHaveDifferentIDs
    /\ ChainA!UpdatedClientsAreCreated
    /\ ChainB!CreatedClientsHaveDifferentIDs
    /\ ChainB!UpdatedClientsAreCreated  
    /\ ClientHeightsAreBelowCounterpartyHeight

=============================================================================
\* Modification History
\* Last modified Wed Apr 14 19:08:27 CEST 2021 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
