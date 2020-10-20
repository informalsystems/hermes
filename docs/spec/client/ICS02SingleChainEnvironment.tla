-------------------- MODULE ICS02SingleChainEnvironment --------------------

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          NrClients, \* number of clients that will be created on the chain
          ClientIDs \* a set of counterparty client IDs for the chain

ASSUME MaxHeight < 10

VARIABLES chainAstore, \* store of ChainA
          datagramsChainA, \* set of datagrams incoming to ChainA
          history \* history variable

vars == <<chainAstore, datagramsChainA, history>>
          
(***************************************************************************
 Instances of ICS02Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE ICS02Chain
          WITH ChainID <- "chainA",
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
            ClientIDs,  
            1..MaxHeight
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
    /\ history = [clientID \in ClientIDs |-> [created |-> FALSE, updated |-> FALSE]]   
    
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
\* Last modified Tue Oct 20 10:12:52 CEST 2020 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
