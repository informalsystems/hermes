-------------------- MODULE ICS02SingleChainEnvironment --------------------

(***************************************************************************
 A TLA+ specification of the IBC client protocol (ICS02). This module models 
 a system consisting of one chain that can create multiple clients, and which 
 operates in an environment that overapproximates the behavior of a correct 
 relayer.    
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS 
    \* @type: Int;
    MaxHeight, \* maximal height of all the chains in the system
    \* @type: Int;
    NrClientsChainA, \* number of clients that will be created on the chain
    \* @type: Set(Str);
    ClientIDsChainA \* a set of counterparty client IDs for the chain

ASSUME MaxHeight < 10

VARIABLES 
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: Set(DATAGRAM);
    datagramsChainA, \* set of datagrams incoming to ChainA
    \* @type: Str -> [created: Bool, updated: Bool];
    history \* history variable

vars == <<chainAstore, datagramsChainA, history>>
          
(***************************************************************************
 Instances of ICS02Chain
 ***************************************************************************)

\* We suppose there is a single chain, ChainA
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               NrClients <- NrClientsChainA,
               ClientIDs <- ClientIDsChainA,
               chainStore <- chainAstore,
               incomingDatagrams <- datagramsChainA               
       
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 
\* non-deterministically create datagrams
CreateDatagrams ==
    \* pick a sequence from the set of client datagrams non-deterministically
    /\ datagramsChainA' \in 
        SUBSET ClientDatagrams(
            ClientIDsChainA, 
            SetHeights(1, MaxHeight)
        )
        
    /\ UNCHANGED <<chainAstore, history>>

    
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
    /\ history = [clientID \in ClientIDsChainA |-> [created |-> FALSE, updated |-> FALSE]]   
    
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
    /\ history \in [ClientIDsChainA -> [created : BOOLEAN, updated : BOOLEAN]]

\* conjunction of invariants
ICS02SingleChainInv ==
    /\ ChainA!CreatedClientsHaveDifferentIDs
    /\ ChainA!UpdatedClientsAreCreated
    
=============================================================================
\* Modification History
\* Last modified Thu Apr 15 12:16:46 CEST 2021 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
