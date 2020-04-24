------------------------------ MODULE relayer ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight \* maximal height of all the chains in the system 

VARIABLES chains, \* a function that assigns a chain record to each chainID
          pendingDatagrams, \* a function that assigns a set of pending datagrams to each chainID
          relayerChainHeights, \* a function that assigns a height to each chainID
          turn         

\* Instance of the environment,  
\* that takes care of the chain logic    
Env == INSTANCE environment 
       WITH chains <- chains, 
            pendingDatagrams <- pendingDatagrams,
            MaxHeight <- MaxHeight
                               
vars == <<chains, pendingDatagrams, relayerChainHeights, turn>>            
envVars == <<chains>>

ChainIDs == Env!ChainIDs
ClientIDs == Env!ClientIDs
Heights == Env!Heights
RelayerClientIDs == Env!ClientIDs

nullClientID == 0
nullHeight == 0 
 

(*** Datagrams ***
    A set of datagrams.
******************)
Datagrams == Env!Datagrams
 
(***************
Chain helper operators
***************) 
\* get the latest height of the chainID
GetLatestHeight(chainID) == Env!GetLatestHeight(chainID)

\* get the client height of the client for the counterparty chain on chainID
GetCounterpartyClientHeight(chainID) == Env!GetCounterpartyClientHeight(chainID)

\* get the ID of the counterparty chain of chainID           
GetCounterpartyChainID(chainID) == Env!GetCounterpartyChainID(chainID) 

\* get the client ID of the client for chainID     
GetClientID(chainID) == Env!GetClientID(chainID)

\* get the client ID of the client for the counterparty chain of chainID
GetCounterpartyClientID(chainID) == Env!GetCounterpartyClientID(chainID)

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chainID) == Env!IsCounterpartyClientOnChain(chainID)

\* returns true if the counterparty client height on chainID is greater or equal than height
CounterpartyClientHeightUpdated(chainID, height) == Env!CounterpartyClientHeightUpdated(chainID, height)

(***************
Client datagrams
****************)     

\* Compute client datagrams for clients for srcChainID on dstChainID
\* Some client updates might trigger an update of the height that 
\* the relayer stores for srcChainID
ClientDatagramsAndRelayerUpdate(srcChainID, dstChainID, relayer) ==
    LET srcChainHeight == GetLatestHeight(srcChainID) IN    
    LET srcClientHeight == GetCounterpartyClientHeight(dstChainID) IN
    LET srcClientID == GetClientID(srcChainID) IN
    
    \* check if the relayer chain height for srcChainID should be updated
    LET srcRelayerChainHeight == 
        IF relayer[srcChainID] < srcChainHeight
        THEN srcChainHeight
        ELSE relayer[srcChainID] IN 
        
    \* create an updated relayer    
    LET updatedRelayer ==
        [relayer EXCEPT ![srcChainID] = srcRelayerChainHeight] IN    
    
    \* generate datagrams for dstChainID
    LET dstDatagrams == 
        IF srcClientHeight = nullHeight
        THEN \* the src client does not exist on dstChainID 
            {[type |-> "CreateClient", 
              height |-> srcChainHeight,
              clientID |-> srcClientID]} 
        ELSE \* the src client exists on dstChainID
            IF srcClientHeight < srcChainHeight
            THEN \* the height of the src client on dstChainID is smaller than the height of the src chain
                {[type |-> "ClientUpdate",
                  height |-> srcChainHeight,
                  clientID |-> srcClientID]} 
            ELSE {} IN                   
                    
    [datagrams|-> dstDatagrams, relayerUpdate |-> updatedRelayer]    
   
\* Compute client datagrams for clients on srcChainID and on dstChainID,
\* as well as the relayer update triggered by creating client datagrams     
ClientDatagrams(srcChainID, dstChainID) ==
    \* get client datagrams for dstChainID 
    \* and relayer update triggered by difference between the height of 
    \* srcChainID and the height that the relayer stores for srcChainID  
    LET dstClientDatagramsAndRelayerUpdate == 
            ClientDatagramsAndRelayerUpdate(srcChainID, dstChainID, relayerChainHeights) IN
    LET dstClientDatagrams == 
            dstClientDatagramsAndRelayerUpdate.datagrams IN
    LET dstRelayerUpdate ==
            dstClientDatagramsAndRelayerUpdate.relayerUpdate IN
    
    \* get client datagrams for srcChainID 
    \* and relayer update triggered by difference between the height of 
    \* dstChainID and the height that the relayer stores for dstChainID
    LET srcClientDatagramsAndRelayerUpdate == 
            ClientDatagramsAndRelayerUpdate(dstChainID, srcChainID, dstRelayerUpdate) IN
    LET srcClientDatagrams == 
            srcClientDatagramsAndRelayerUpdate.datagrams IN
    LET srcRelayerUpdate == 
            srcClientDatagramsAndRelayerUpdate.relayerUpdate IN     
            
    [src |-> srcClientDatagrams, dst |-> dstClientDatagrams, relayerUpdate |-> srcRelayerUpdate]            
    
(***************
Connection datagrams
****************)

ConnectionDatagrams(srcChainID, dstChainID) ==
    \* TODO
    [src |-> {}, dst |-> {}]

(***************
Channel datagrams
****************)

ChannelDatagrams(srcChainID, dstChainID) ==
    \* TODO
    [src |-> {}, dst |-> {}]    

(****************
Compute pending datagrams
****************)

\* Currently, only supporting ICS 002: Client updates
\* TODO: Support the remaining datagrams
PendingDatagrams(srcChainID, dstChainID) ==
    \* ICS 002 : Clients
    \* - Determine if light clients needs to be updated
    LET clientDatagrams == ClientDatagrams(srcChainID, dstChainID) IN
    
    \* ICS3 : Connections
    \* - Determine if any connection handshakes are in progress
    LET connectionDatagrams == ConnectionDatagrams(srcChainID, dstChainID) IN
    
    \* ICS4 : Channels & Packets
    \* - Determine if any packets, acknowledgements, or timeouts need to be relayed
    LET channelDatagrams == ChannelDatagrams(srcChainID, dstChainID) IN
    
    [src |-> clientDatagrams.src \union connectionDatagrams.src \union channelDatagrams.src, 
     dst |-> clientDatagrams.dst \union connectionDatagrams.dst \union channelDatagrams.dst,
     relayerUpdate |-> clientDatagrams.relayerUpdate] 
             
\* TODO: pending datagrams per direction?              
  
(***************
Relayer actions
***************)   

\* Update the height of the relayer client for some chainID
UpdateRelayerClients ==
    \E chainID \in ChainIDs : 
        /\ relayerChainHeights[chainID] < GetLatestHeight(chainID)
        /\ relayerChainHeights' = [relayerChainHeights EXCEPT 
                                        ![chainID] = GetLatestHeight(chainID)
                                   ]
        /\ UNCHANGED <<chains, pendingDatagrams>>  

\* for two chains, srcChainID and dstChainID,
\* where srcChainID /= dstChainID, and where the 
\* relayer clients for srcChainID and dstChainID 
\* are initialized (i.e., their height is not nullHeight),  
\* create the pending datagrams and update the 
\* corresponding sets of pending datagrams
Relay ==
    \E srcChainID \in ChainIDs :
        \E dstChainID \in ChainIDs :
            /\ srcChainID /= dstChainID
            /\ LET datagramsAndRelayerUpdate == PendingDatagrams(srcChainID, dstChainID) IN
                  /\ pendingDatagrams' = 
                        [pendingDatagrams EXCEPT 
                            ![srcChainID] = pendingDatagrams[srcChainID] \union datagramsAndRelayerUpdate.src, 
                            ![dstChainID] = pendingDatagrams[dstChainID] \union datagramsAndRelayerUpdate.dst
                        ]
                  /\ relayerChainHeights' = datagramsAndRelayerUpdate.relayerUpdate       
                  /\ UNCHANGED chains
            
(***************
Component actions
***************)  
                 
\* Relayer
\*    The relayer either
\*        - updates its clients, or
\*        - relays datagrams between two chains, or
\*        - does nothing
Relayer ==
    \/ UpdateRelayerClients
    \/ Relay
    \/ UNCHANGED vars
    
\* Environment
\*    The environment takes the action Env!Next
\*    and leaves the relayer variable unchanged
Environment ==
    /\ Env!Next
    /\ UNCHANGED relayerChainHeights    

(***************
Specification
***************) 
    
\* Initial state predicate
\*    Initially
\*        - it is either the relayer's or the environment's turn
\*        - the relayer chain heights are uninitialized 
\*          (i.e., their height is nullHeight)
\*        - the environment is initialized, by Env!Init    
Init == 
    /\ turn \in {"relayer", "environment"}
    /\ relayerChainHeights = [chainID \in ChainIDs |-> nullHeight]
    /\ Env!Init    
    
\* Next state action
\*    The system consists of two components: relayer and environment.
\*    In the system, the relayer and environment 
\*    take alternate steps
Next ==
    \/ /\ turn = "relayer"
       /\ Relayer
       /\ turn' = "environment"
    \/ /\ turn = "environment"
       /\ Environment
       /\ turn' = "relayer"     
       
\* Fairness constraints
Fairness ==
    /\ WF_<<chains, pendingDatagrams, relayerChainHeights>>(UpdateRelayerClients)
    /\ WF_<<chains, pendingDatagrams, relayerChainHeights>>(Relay)
    /\ Env!Fairness 
                        
\* Spec formula
Spec == Init /\ [][Next]_vars /\ Fairness   

(************
Helper operators used in properties
************)

\* returns true if there is a "CreateClient" datagram
\* in the pending datagrams for chainID and height h 
IsCreateClientInPendingDatagrams(chainID, clID, h) == 
    [type |-> "CreateClient", clientID |-> clID, height |-> h] 
        \in pendingDatagrams[chainID]

\* returns true if there is a "ClientUpdate" datagram
\* in the pending datagrams for chainID and height h           
IsClientUpdateInPendingDatagrams(chainID, clID, h) ==
    [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
        \in pendingDatagrams[chainID]

(************
Invariants
************)

\* Type invariant
TypeOK ==
    /\ turn \in {"relayer", "environment"}
    /\ relayerChainHeights \in [ChainIDs -> Heights \union {nullHeight}]
    /\ Env!TypeOK
    
\* CreateClientInv   
\* if a "CreateClient" datagram is in pendingDatagrams for chainID, 
\* then the clientID of the datagram is the counterparty clientID for chainID
CreateClientInv ==
    \A chainID \in ChainIDs : \A clID \in ClientIDs : 
        ((\E h \in Heights : IsCreateClientInPendingDatagrams(chainID, clID, h)) 
            => (clID = GetCounterpartyClientID(chainID)))

\* if a "ClientUpdate" datagram is in pendingDatagrams for chainID, 
\* then the clientID of the datagram is the counterparty clientID for chainID  
ClientUpdateInv ==
    \A chainID \in ChainIDs : \A clID \in ClientIDs : \A h \in Heights :
        IsClientUpdateInPendingDatagrams(chainID, clID, h) 
            => clID = GetCounterpartyClientID(chainID)

\* Inv
\* A conjunction of all invariants                            
Inv ==
    /\ TypeOK
    /\ CreateClientInv
    /\ ClientUpdateInv                            
  
(************
Properties
************)

\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the counterparty client is not initialized
\*  - then
\*      * the relayer EVENTUALLY adds a "CreateClient" datagram in pending datagrams of chainID
CreateClientIsGenerated == 
    [](\A chainID \in ChainIDs : 
        GetCounterpartyClientHeight(chainID) = nullHeight
        => <>(\E h \in Heights : IsCreateClientInPendingDatagrams(chainID, GetCounterpartyClientID(chainID), h)))
        
\* it ALWAYS holds that, for every chainID:
\*    - if   
\*        * there is a "CreateClient" datagram in pending datagrams of chainID for some height h
\*        * a counterparty client does not exist on chainID
\*    - then 
\*        * the counterparty client is EVENTUALLY created on chainID 
ClientCreated ==
    [](\A chainID \in ChainIDs :  
        (/\ \E h \in Heights : IsCreateClientInPendingDatagrams(chainID, GetCounterpartyClientID(chainID), h) 
         /\ ~IsCounterpartyClientOnChain(chainID))
           => (<>(IsCounterpartyClientOnChain(chainID))))  

\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the counterparty client on chainID has height smaller 
\*        than the height of chainID's counterparty chain
\*  - then
\*      * the relayer EVENTUALLY adds a "ClientUpdate" datagram in pending datagrams of chainID           
ClientUpdateIsGenerated ==
    [](\A chainID \in ChainIDs : \A h1 \in Heights : 
        (/\ GetCounterpartyClientHeight(chainID) = h1
         /\ GetCounterpartyClientHeight(chainID) < GetLatestHeight(GetCounterpartyChainID(chainID)))
            => <>(\E h2 \in Heights : 
                    /\ h1 <= h2 
                    /\ IsClientUpdateInPendingDatagrams(chainID, GetCounterpartyClientID(chainID), h2)))           

\* it ALWAYS holds that, for every chainID:
\*    - if   
\*        * there is a "ClientUpdate" datagram in pending datagrams of chainID 
\*          for height h
\*        * the counterparty client height is smaller than h
\*    - then 
\*        * the counterparty client height is EVENTUALLY udpated to at least h  
ClientUpdated ==
    [](\A chainID \in ChainIDs : \A h \in Heights : 
        (/\ IsClientUpdateInPendingDatagrams(chainID, GetCounterpartyClientID(chainID), h) 
         /\ GetCounterpartyClientHeight(chainID) < h)
           => (<>(CounterpartyClientHeightUpdated(chainID, h))))

\* for every chainID, it is always the case that the height of the chain
\* does not decrease                      
HeightsDontDecrease ==
    [](\A chainID \in ChainIDs : \A h \in Heights :
        (chains[chainID].height = h) 
            => <>(chains[chainID].height >= h))           
                                 
=============================================================================
\* Modification History
\* Last modified Thu Apr 02 18:33:51 CEST 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
