---------------------------- MODULE NewEnvironment ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight \* maximal height of all the chains in the system 

VARIABLES chainA,
          chainB,
          incomingDatagramsChainA, 
          incomingDatagramsChainB, 
          relayer1Heights,
          relayer2Heights,
          outgoingDatagrams

vars == <<chainAstore, chainBstore, 
          incomingDatagramsChainA, incomingDatagramsChainB,
          relayer1Heights, relayer2Heights,
          outgoingDatagrams>>


\* We suppose there are two correct relayers in the system, Relayer1 and Relayer2
Relayer1 == INSTANCE Relayer
            WITH GenerateClientDatagrams <- (GenerateClientDatagrams + 1) % 2,
                 GenerateConnectionDatagrams <- (GenerateConnectionDatagrams + 1) % 2,
                 GenerateChannelDatagrams <- (GenerateChannelDatagrams + 1) % 2,
                 MaxHeight <- MaxHeight,
                 chains <- ["chainA" |-> chainAstore, "chainB" |-> chainBstore],
                 relayerHeights <- relayer1Heights
                 
Relayer2 == INSTANCE Relayer
            WITH GenerateClientDatagrams <- (GenerateClientDatagrams + 1) / 2,
                 GenerateConnectionDatagrams <- (GenerateConnectionDatagrams + 1) / 2,
                 GenerateChannelDatagrams <- (GenerateChannelDatagrams + 1) / 2,
                 MaxHeight <- MaxHeight,
                 chains <- ["chainA" |-> chainAstore, "chainB" |-> chainBstore],
                 relayerHeights <- relayer2Heights

\* We suppose there are two chains that communicate, ChainA and ChainB
ChainA == INSTANCE Chain
          WITH MaxHeight <- MaxHeight,
               chainStore <- chainA,
               incomingDatagrams <- incomingDatagramsChainA

ChainB == INSTANCE Chain
          WITH MaxHeight <- MaxHeight,
               chainStore <- chainB,
               incomingDatagrams <- incomingDatagramsChainB

DeliverDatagrams ==
    /\ incomingDatagramsChainA' = incomingDatagramsChainA \cup outgoingDatagrams["chainA"]
    /\ incomingDatagramsChainB' = incomingDatagramsChainA \cup outgoingDatagrams["chainB"]
    /\ outgoingDatagrams' = [chainID \in ChainIDs |-> {}]
    /\ UNCHANGED <<chainAstore, chainBstore, relayer1Heights, relayer2Heights>>

\* TODO
FaultyRelayer ==
    TRUE
(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    /\ Relayer1!Init
    /\ Relayer2!Init

\* Next state action
Next ==
    \/ ChainA!Next
    \/ ChainB!Next
    \/ Relayer1!Next
    \/ Relayer2!Next
    \/ DeliverDatagrams
    \* \/ FaultyRelayer

Fairness ==
    WF_vars(Next)    

=============================================================================
\* Modification History
\* Last modified Mon Jun 08 16:48:22 CET 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:48:22 CET 2020 by ilinastoilkovska
