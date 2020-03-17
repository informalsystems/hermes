------------------------------ MODULE relayer ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight, \* maximal height of all the chains in the system 
          NrChains \* number of chains in the system

VARIABLES chains, \* a function that assigns to each chainID a chain record
          pendingDatagrams, \* a function that assigns to each chainID a set of pending datagrams
          relayer, \* a relayer record
          turn

\* Instance of the environment,  
\* that takes care of the chain logic    
Env == INSTANCE environment 
       WITH chains <- chains, 
            pendingDatagrams <- pendingDatagrams,
            MaxHeight <- MaxHeight,
            NrChains <- NrChains
                               
vars == <<chains, pendingDatagrams, relayer, turn>>            

ChainIDs == 1..NrChains
ClientIDs == 1..(NrChains * NrChains)
Heights == 1..MaxHeight
RelayerClientIDs == 1..NrChains

nullClientID == 0
nullHeight == 0 
 
(***************
Client ID operators
***************)

GetChainIDs(clientID) == Env!GetChainIDs(clientID)
    
GetClientID(onChainID, forChainID) == Env!GetClientID(onChainID, forChainID)
    
ValidClientID(chainID, clientID) == Env!ValidClientID(chainID, clientID) 
 
(***************
Client datagrams
****************) 
 
\* get the latest height of the chainID
GetLatestHeight(chainID) ==
    chains[chainID].height    
    
\* get the client height of the client on chain srcChainID for chain dstChainID    
GetClientHeight(srcChainID, dstChainID) ==
    chains[srcChainID].clientHeights[dstChainID]

ClientDatagrams(srcChainID, dstChainID) ==
    LET dstChainHeight == GetLatestHeight(dstChainID) IN    
    LET dstClientHeight == GetClientHeight(srcChainID, dstChainID) IN
    LET srcDatagrams == 
        IF dstClientHeight = nullHeight
        THEN \* the dst client does not exist at the src chain 
            {[type |-> "CreateClient", 
              height |-> relayer.clientHeights[dstChainID],
              clientID |-> GetClientID(srcChainID, dstChainID)]} 
        ELSE \* the dst client exists at the src chain
            IF dstClientHeight < dstChainHeight
            THEN \* the height of the dst client is smaller than the height of the dst chain
                {[type |-> "ClientUpdate",
                  height |-> relayer.clientHeights[dstChainID],
                  clientID |-> GetClientID(srcChainID, dstChainID)]} 
            ELSE {} IN
                    
    LET srcChainHeight == GetLatestHeight(srcChainID) IN    
    LET srcClientHeight == GetClientHeight(dstChainID, srcChainID) IN
    LET dstDatagrams == 
        IF srcClientHeight = nullHeight
        THEN \* the src client does not exist at the dst chain 
            {[type |-> "CreateClient", 
              height |-> relayer.clientHeights[srcChainID],
              clientID |-> GetClientID(dstChainID, srcChainID)]} 
        ELSE \* the src chain exists at the dst chain
            IF srcClientHeight < srcChainHeight
            THEN \* the height of the src client is smaller than the height of the src chain
                {[type |-> "ClientUpdate",
                  height |-> relayer.clientHeights[srcChainID],
                  clientID |-> GetClientID(dstChainID, srcChainID)]} 
            ELSE {} IN                    
                    
    [src |-> srcDatagrams, dst |-> dstDatagrams]

(****************
Compute pending datagrams
****************)

\* Currently, only supporting ICS2: Client updates
\* TODO: Support the remaining datagrams
PendingDatagrams(srcChainID, dstChainID) ==
    \* ICS2 : Clients
    \* - Determine if light clients needs to be updated 
    LET clientDatagrams == ClientDatagrams(srcChainID, dstChainID) IN
    
   [src |-> clientDatagrams.src,
    dst |-> clientDatagrams.dst] 

    
  
(***************
Relayer actions
***************)   

\* Update the height of the relayer client for some chainID
UpdateRelayerClients ==
    \E chainID \in ChainIDs : 
        /\ relayer.clientHeights[chainID] < chains[chainID].height
        /\ relayer' = [relayer EXCEPT 
                         !.clientHeights = [relayer.clientHeights EXCEPT 
                                                ![chainID] = chains[chainID].height
                                           ]
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
            /\ relayer.clientHeights[srcChainID] /= nullHeight
            /\ relayer.clientHeights[dstChainID] /= nullHeight
            /\ LET datagrams == PendingDatagrams(srcChainID, dstChainID) IN
                  /\ pendingDatagrams' = 
                        [pendingDatagrams EXCEPT 
                            ![srcChainID] = pendingDatagrams[srcChainID] \union datagrams.src, 
                            ![dstChainID] = pendingDatagrams[dstChainID] \union datagrams.dst
                        ]
                  /\ UNCHANGED <<chains, relayer>>
            
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
    /\ UNCHANGED relayer    

(***************
Specification
***************) 
    
\* Initial state predicate
\*    Initially
\*        - it is either the relayer's or the environment's turn
\*        - the relayer clients are uninitialized (i.e., their height 
\*          is nullHeight  
\*        - the environment is initialized, by Env!Init    
Init == 
    /\ turn \in {"relayer", "environment"}
    /\ relayer = [clientHeights |-> [chainID \in ChainIDs |-> nullHeight]]
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
    /\ WF_<<chains, pendingDatagrams, relayer>>(UpdateRelayerClients)
    /\ WF_<<chains, pendingDatagrams, relayer>>(Relay)
    /\ Env!Fairness 
                        
\* Spec formula
Spec == Init /\ [][Next]_vars /\ Fairness   

(************
Invariants
************)

\* Type invariant
TypeOK ==
    /\ turn \in {"relayer", "environment"}
    /\ relayer \in [clientHeights : [ChainIDs -> Heights \union {nullHeight}]]
    /\ Env!TypeOK
    
\* CreateClientInv   
\* if a "CreateClient" datagram is in pendingDatagrams for chainID, 
\* then the clientID of the datagram is a valid client ID w.r.t. chainID    
CreateClientInv ==
    \A chainID \in ChainIDs : \A clID \in ClientIDs : \A h \in Heights :
        [type |-> "CreateClient", clientID |-> clID, height |-> h] \in pendingDatagrams[chainID] 
            => ValidClientID(chainID, clID)

\* if a "ClientUpdate" datagram is in pendingDatagrams for chainID, 
\* then the clientID of the datagram is a valid client ID w.r.t. chainID    
ClientUpdateInv ==
    \A chainID \in ChainIDs : \A clID \in ClientIDs : \A h \in Heights :
        [type |-> "ClientUpdate", clientID |-> clID, height |-> h] \in pendingDatagrams[chainID] 
            => ValidClientID(chainID, clID)

                                 
=============================================================================
\* Modification History
\* Last modified Tue Mar 17 17:27:03 CET 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
