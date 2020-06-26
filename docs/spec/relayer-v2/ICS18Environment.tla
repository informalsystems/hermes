-------------------------- MODULE ICS18Environment --------------------------

EXTENDS Naturals, FiniteSets, RelayerDefinitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          ClientDatagramsRelayer1, \* toggle generation of client datagrams for Relayer1 
          ClientDatagramsRelayer2, \* toggle generation of client datagrams for Relayer2
          ConnectionDatagramsRelayer1, \* toggle generation of connection datagrams for Relayer1
          ConnectionDatagramsRelayer2, \* toggle generation of connection datagrams for Relayer2
          ChannelDatagramsRelayer1, \* toggle generation of channel datagrams for Relayer1
          ChannelDatagramsRelayer2 \* toggle generation of channel datagrams for Relayer2

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          incomingDatagramsChainA, \* set of datagrams incoming to ChainA
          incomingDatagramsChainB, \* set of datagrams incoming to ChainB
          relayer1Heights, \* the client heights of Relayer1
          relayer2Heights, \* the client heights of Relayer2
          outgoingDatagrams \* sets of datagrams outgoing of the relayers
          
vars == <<chainAstore, chainBstore, 
          incomingDatagramsChainA, incomingDatagramsChainB,
          relayer1Heights, relayer2Heights,
          outgoingDatagrams>>
chainAvars == <<chainAstore, incomingDatagramsChainA>>
chainBvars == <<chainBstore, incomingDatagramsChainB>>
relayerVars == <<relayer1Heights, relayer2Heights, outgoingDatagrams>>

Heights == 1..MaxHeight \* set of possible heights of the chains in the system

(***************************************************************************
 Instances of Relayer and Chain
 ***************************************************************************)

\* We suppose there are two correct relayers in the system, Relayer1 and Relayer2
\* Relayer1 -- Instance of Relayer.tla
Relayer1 == INSTANCE Relayer
            WITH GenerateClientDatagrams <- ClientDatagramsRelayer1,
                 GenerateConnectionDatagrams <- ConnectionDatagramsRelayer1,
                 GenerateChannelDatagrams <- ChannelDatagramsRelayer1,
                 Heights <- Heights,
                 chainAstore <- chainAstore,
                 chainBstore <- chainBstore,
                 relayerHeights <- relayer1Heights
                 
\* Relayer2 -- Instance of Relayer.tla      
Relayer2 == INSTANCE Relayer
            WITH GenerateClientDatagrams <- ClientDatagramsRelayer2,
                 GenerateConnectionDatagrams <- ConnectionDatagramsRelayer2,
                 GenerateChannelDatagrams <- ChannelDatagramsRelayer2,
                 Heights <- Heights,
                 chainAstore <- chainAstore,
                 chainBstore <- chainBstore,
                 relayerHeights <- relayer2Heights

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               Heights <- Heights,
               chainStore <- chainAstore,
               incomingDatagrams <- incomingDatagramsChainA

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               Heights <- Heights,
               chainStore <- chainBstore,
               incomingDatagrams <- incomingDatagramsChainB

(***************************************************************************
 Component actions
 ***************************************************************************)

\* RelayerAction: either correct relayer takes a step, leaving the other 
\* variables unchanged 
RelayerAction ==
    \/ /\ Relayer1!Next
       /\ UNCHANGED chainAvars
       /\ UNCHANGED chainBvars
       /\ UNCHANGED relayer2Heights
    \/ /\ Relayer2!Next  
       /\ UNCHANGED chainAvars
       /\ UNCHANGED chainBvars
       /\ UNCHANGED relayer1Heights 

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchanged       
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
       /\ UNCHANGED relayerVars
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars
       /\ UNCHANGED relayerVars  

(***************************************************************************
 ICS18Environment actions
 ***************************************************************************)
\* Submit datagrams from relayers to chains
SubmitDatagrams ==
    /\ incomingDatagramsChainA' = incomingDatagramsChainA \cup outgoingDatagrams["chainA"]
    /\ incomingDatagramsChainB' = incomingDatagramsChainB \cup outgoingDatagrams["chainB"]
    /\ outgoingDatagrams' = [chainID \in ChainIDs |-> {}]
    /\ UNCHANGED <<chainAstore, chainBstore, relayer1Heights, relayer2Heights>>

\* Faulty relayer action
FaultyRelayer ==
\*    TODO  
    TRUE
    
EnvironmentAction ==
    \/ SubmitDatagrams
\*    TODO: Uncomment once FaultyRelayer is specified
\*    \/ FaultyRelayer
        
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
    \/ ChainAction
    \/ RelayerAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
    
   
\* Fairness constraint
Fairness ==
    /\ WF_vars(SubmitDatagrams)  
    /\ ChainA!Fairness
    /\ ChainB!Fairness
    /\ Relayer1!Fairness
    /\ Relayer1!Fairness

\* Specification formula
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************
 Invariants
 ***************************************************************************)

\* Type invariant
TypeOK ==
    /\ ChainA!TypeOK
    /\ ChainB!TypeOK
    /\ Relayer1!TypeOK
    /\ Relayer2!TypeOK

(***************************************************************************
 Helper operators used in properties
 ***************************************************************************)
\* get chain store by ID
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
        
\* returns true if there is a "ClientUpdate" datagram
\* in the incoming datagrams for chainID           
IsClientUpdateInIncomingDatagrams(chainID, h) ==
    LET clID == GetCounterpartyClientID(chainID) IN
    IF chainID = "chainA"
    THEN [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
            \in incomingDatagramsChainA
    ELSE [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
            \in incomingDatagramsChainB
   
\* returns true if there is a "ClientUpdate" datagram
\* in the outgoing datagrams for chainID             
IsClientUpdateInOutgoingDatagrams(chainID, h) ==
    LET clID == GetCounterpartyClientID(chainID) IN
    [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
        \in outgoingDatagrams[chainID]            
            
\* returns true if there is a "ConnOpenInit" datagram 
\* in outgoing datagrams for chainID
IsConnOpenInitInOutgoingDatagrams(chainID) ==
    LET clID == GetClientID(chainID) IN
    LET counterpartyClID == GetCounterpartyClientID(chainID) IN 
    LET connID == GetConnectionID(chainID) IN
    LET counterpartyConnID == GetCounterpartyConnectionID(chainID) IN
    
    [type |-> "ConnOpenInit", 
     connectionID |-> connID, 
     clientID |-> clID,
     counterpartyConnectionID |-> counterpartyConnID,
     counterpartyClientID |-> counterpartyClID] \in outgoingDatagrams[chainID]
            
\* returns true if there is a "ChanOpenInit" datagram  
\* in outgoing datagrams for chainID
IsChanOpenInitInOutgoingDatagrams(chainID) ==
    LET chanID == GetChannelID(chainID) IN
    LET counterpartyChanID == GetCounterpartyChannelID(chainID) IN
    [type |-> "ChanOpenInit", 
     channelID |-> chanID, 
     counterpartyChannelID |-> counterpartyChanID] \in outgoingDatagrams[chainID]
               
----------------------------------------------------------------------------
(***************************************************************************
 Properties
 ***************************************************************************)
(***************************************************************************
 Safety
 ***************************************************************************)    

\* it ALWAYS holds that, for every chainID and every height h:
\*  - if 
\*    * there is a "ClientUpdate" datagram for chainID and height h and 
\*    * the height h is smaller than the maximal counterparty client height 
\*      at chainID
\*  - then 
\*    * the height h is NEVER added to the counterparty client heights 
ClientUpdateSafety ==
    [](\A chainID \in ChainIDs : \A h \in Heights : 
       (/\ IsClientUpdateInIncomingDatagrams(chainID, h)
        /\ h < GetMaxCounterpartyClientHeight(GetChainByID(chainID)))
        => [](~IsCounterpartyClientHeightOnChain(GetChainByID(chainID), h)))

(***************************************************************************
 Safety [ICS18Safety]:
    Bad datagrams are not used to update the chain stores 
 ***************************************************************************)
\* ICS18Safety property: conjunction of safety properties 
ICS18Safety ==
    /\ ClientUpdateSafety  
    \* TODO: similar properties for connection, channel handshake datagrams      

(***************************************************************************
 Liveness: Eventual delivery of client datagrams
 ***************************************************************************)
 
\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the counterparty client is not initialized
\*  - then
\*      * the chain EVENTUALLY creates the counterparty client
CreateClientDelivery == 
    [](\A chainID \in ChainIDs : 
        (GetCounterpartyClientHeights(GetChainByID(chainID)) = {})
        => <>(IsCounterpartyClientOnChain(GetChainByID(chainID))))

\* it ALWAYS holds that, for every chainID and every height h
\*  - if 
\*      * EVENTUALLY a ClientUpdate for height h is sent to chainID
\*  -  then 
\*      * EVENTUALLY height h is added to counterparty client heights of chainID
ClientUpdateDelivery ==
    [](\A chainID \in ChainIDs : \A h \in Heights :
       (<>IsClientUpdateInOutgoingDatagrams(chainID, h)   
            => <>(IsCounterpartyClientHeightOnChain(GetChainByID(chainID), h))))
 
(***************************************************************************
 Liveness: Eventual delivery of connection datagrams
 ***************************************************************************)
 
\* it ALWAYS holds that, for every chainID
\*  - if 
\*      * EVENTUALLY a ConnOpenInit is sent to chainID
\*  -  then 
\*      * EVENTUALLY the connections at chainID and its counterparty are open 
 ConnOpenInitDelivery ==
    [](\A chainID \in ChainIDs : 
       (<>IsConnOpenInitInOutgoingDatagrams(chainID) 
          => <>(/\ IsConnectionOpen(GetChainByID(chainID))
                /\ IsConnectionOpen(GetChainByID(GetCounterpartyChainID(chainID))))))   
         
(***************************************************************************
 Liveness: Eventual delivery of channel datagrams
 ***************************************************************************)
 \* it ALWAYS holds that, for every chainID
\*  - if 
\*      * EVENTUALLY a ChanOpenInit is sent to chainID
\*  -  then 
\*      * EVENTUALLY the channels at chainID and its counterparty are open
 ChanOpenInitDelivery ==
    [](\A chainID \in ChainIDs : 
       (<>IsChanOpenInitInOutgoingDatagrams(chainID) 
          => <>(/\ IsChannelOpen(GetChainByID(chainID))
                /\ IsChannelOpen(GetChainByID(GetCounterpartyChainID(chainID))))))   
 
(***************************************************************************
 Liveness [ICS18Delivery]: 
    If ChainA sends a datagram to ChainB, then ChainB eventually receives 
    the datagram
                   
 * ChainA sends a datagram iff a correct relayer constructs the datagram by 
   scanning ChainA's store
 * ChainB receives a datagram iff it acts upon this datagram
 ***************************************************************************)            
\* ICS18Delivery property: conjunction of delivery properties 
ICS18Delivery ==
    \* at least one relayer creates client datagrams
    /\ (ClientDatagramsRelayer1 \/ ClientDatagramsRelayer2)
         => /\ CreateClientDelivery
            /\ ClientUpdateDelivery
    \* at least one relayer creates connection datagrams
    /\ (ConnectionDatagramsRelayer1 \/ ConnectionDatagramsRelayer2)
         => ConnOpenInitDelivery 
    \* at least one relayer creates channel datagrams
    /\ (ChannelDatagramsRelayer1 \/ ChannelDatagramsRelayer2)
         => ChanOpenInitDelivery
               
=============================================================================
\* Modification History
\* Last modified Fri Jun 26 14:51:59 CEST 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:48:22 CET 2020 by ilinastoilkovska
