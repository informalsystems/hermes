-------------------------- MODULE ICS20Environment --------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          MaxPacketSeq, \* maximal packet sequence number
          EscrowAddressesChainA, \* a set of escrow addresses for ChainA
          EscrowAddressesChainB, \* a set of escrow addresses for ChainB
          DenominationChainA, \* denomination of tokens at ChainA
          DenominationChainB \* denomination of tokens at ChainA

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          packetDatagramsChainA, \* set of packet datagrams incoming to ChainA
          packetDatagramsChainB, \* set of packet datagrams incoming to ChainB
          packetLog, \* packet log
          appPacketSeqChainA, \* packet sequence number from the application on ChainA
          appPacketSeqChainB, \* packet sequence number from the application on ChainB
          history \* history variable

chainAvars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA, history, packetLog>>
chainBvars == <<chainBstore, packetDatagramsChainB, appPacketSeqChainB, history, packetLog>>
vars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA,
          chainBstore, packetDatagramsChainB, appPacketSeqChainB,
          history, packetLog>>
          
(***************************************************************************
 Instances of ICS20Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of ICS20Chain.tla
ChainA == INSTANCE ICS20Chain
          WITH ChainID <- "chainA",
               EscrowAddresses <- EscrowAddressesChainA,
               Denomination <- DenominationChainA,
               chainStore <- chainAstore,
               incomingPacketDatagrams <- packetDatagramsChainA,    
               appPacketSeq <- appPacketSeqChainA    

\* ChainB -- Instance of ICS20Chain.tla
ChainB == INSTANCE ICS20Chain
          WITH ChainID <- "chainB",
               EscrowAddresses <- EscrowAddressesChainB,
               Denomination <- DenominationChainB,
               chainStore <- chainBstore,
               incomingPacketDatagrams <- packetDatagramsChainB,
               appPacketSeq <- appPacketSeqChainB
               
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 
\* non-deterministically create datagrams
CreateDatagrams ==
    /\ TRUE \* todo
        
    /\ UNCHANGED <<chainAstore, chainBstore>>
    /\ UNCHANGED history                       
    
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchange
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
    \* todo: find out what needs to be tracked in history
    /\ history = FALSE
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
    
                      

=============================================================================
\* Modification History
\* Last modified Thu Oct 29 19:20:18 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:00:24 CEST 2020 by ilinastoilkovska
