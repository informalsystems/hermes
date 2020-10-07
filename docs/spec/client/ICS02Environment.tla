-------------------------- MODULE ICS02Environment --------------------------

EXTENDS Integers, FiniteSets, Sequences, ICS02Definitions

CONSTANTS MaxHeight \* maximal height of all the chains in the system

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          incomingDatagramsChainA, \* set of datagrams incoming to ChainA
          incomingDatagramsChainB, \* set of datagrams incoming to ChainB
          outgoingDatagrams \* sets of datagrams outgoing of the relayers

chainAvars == <<chainAstore, incomingDatagramsChainA>>
chainBvars == <<chainBstore, incomingDatagramsChainB>>
vars == <<chainAstore, incomingDatagramsChainA, chainBstore, incomingDatagramsChainB, outgoingDatagrams>>
          
(***************************************************************************
 Instances of ICS02Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE ICS02Chain
          WITH ChainID <- "chainA",
               chainStore <- chainAstore,
               incomingDatagrams <- incomingDatagramsChainA

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE ICS02Chain
          WITH ChainID <- "chainB",
               chainStore <- chainBstore,
               incomingDatagrams <- incomingDatagramsChainB
               
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore         
       
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 
\* non-deterministically create outgoing datagrams
CreateDatagrams ==
    /\ \/ chainAstore.height < MaxHeight
       \/ chainBstore.height < MaxHeight
    \* pick a sequence from the set of sequences of client datagrams non-deterministically
    \* for each chain
    /\ \A chainID \in ChainIDs :  
        outgoingDatagrams[chainID] = AsSetDatagrams({}) 
    /\ outgoingDatagrams' \in [ChainIDs -> (SUBSET Datagrams(MaxHeight))]
    /\ \A chainID \in ChainIDs :
        outgoingDatagrams'[chainID] 
        \subseteq 
        ClientDatagrams(MaxHeight, GetCounterpartyClientID(chainID), GetLatestHeight(GetChainByID(chainID)))
    /\ UNCHANGED <<chainAstore, chainBstore, incomingDatagramsChainA, incomingDatagramsChainB>>        
       
\* Submit datagrams from relayers to chains
SubmitDatagrams ==
    /\ incomingDatagramsChainA' = AsSeqDatagrams(incomingDatagramsChainA \union outgoingDatagrams["chainA"])
    /\ incomingDatagramsChainB' = AsSeqDatagrams(incomingDatagramsChainB \union outgoingDatagrams["chainB"])
    /\ outgoingDatagrams' = [chainID \in ChainIDs |-> AsSetDatagrams({})]
    /\ UNCHANGED <<chainAstore, chainBstore>>
    
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchanged       
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
       /\ UNCHANGED outgoingDatagrams
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars
       /\ UNCHANGED outgoingDatagrams
       
EnvironmentAction ==
    \/ CreateDatagrams
    \/ SubmitDatagrams      
    
(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init    
    /\ outgoingDatagrams = [chainID \in ChainIDs |-> AsSetDatagrams({})]
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars    
    
\* Specification formula
Spec == Init /\ [][Next]_vars    
    
=============================================================================
\* Modification History
\* Last modified Wed Oct 07 12:42:10 CEST 2020 by ilinastoilkovska
\* Created Fri Oct 02 12:57:19 CEST 2020 by ilinastoilkovska
