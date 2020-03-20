---------------------------- MODULE environment ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          NrChains \* number of chains in the system 

VARIABLES chains, \* a function that assigns to each chainID a chain record 
          pendingDatagrams \* a function that assigns to each chainID a set of pending datagrams
          
vars == <<chains, pendingDatagrams>>

ChainIDs == 1..NrChains
ClientIDs == 1..(NrChains * NrChains)
Heights == 1..MaxHeight

nullClientID == 0
nullHeight == 0

Max(S) == CHOOSE x \in S: \A y \in S: y <= x    

(*** Chains ***
    A set of chain records. 
    A chain record contains the following fields:
    
    - height : an integer between 1 and MaxHeight. 
      Stores the current height of the chain.
    
    - clientHeights : a function that maps chain identifiers to heights.
      Stores the height of the clients for all other chains on this chain.
**************)
Chains ==    
    [
        height : Heights \union {nullHeight},
        clientHeights : [ChainIDs -> Heights \union {nullHeight}]
    ]
    
(*** Datagrams ***
    A set of datagrams.
******************)
Datagrams ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : Heights]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights]    

(***************
Client ID operators
***************)

\* given a clientID, translate back to srcChainID and dstChainID
GetChainIDs(clientID) ==
    LET srcChainID == (clientID - 1) \div NrChains + 1 IN
    LET dstChainID == ((clientID - 1) % NrChains) + 1 IN
    [src |-> srcChainID, dst |-> dstChainID]
    
\* get the clientID of the client on the chain onChainID, for the chain forChainID
GetClientID(onChainID, forChainID) ==
    (onChainID - 1) * NrChains + forChainID
    
\* check if the clientID is a valid client ID w.r.t. chainID    
ValidClientID(chainID, clientID) ==
    /\ GetChainIDs(clientID).src = chainID
    /\ GetChainIDs(clientID).dst \in ChainIDs 
    
(***************
Chain update operators
***************)    

LightClientUpdate(chainID, chain, datagrams) == 
    \* update chain with "CreateClient" datagrams
    LET createClients == {dgr \in datagrams : dgr.type = "CreateClient"} IN
    LET createClientIDs == {clientID \in ClientIDs : 
            /\ \E dgr \in createClients : dgr.clientID = clientID
            /\ ValidClientID(chainID, clientID)} IN
    LET createClientHeights(clientID) == 
            {h \in Heights : 
                \E dgr \in createClients : 
                    dgr.clientID = clientID /\ dgr.height = h} IN  
    
    \* new chain record with clients created
    LET clientsCreated == [
            height |-> chain.height,
            clientHeights |-> 
                [cID \in ChainIDs |-> IF GetClientID(chainID, cID) \in createClientIDs
                                      THEN Max(createClientHeights(GetClientID(chainID, cID)))
                                      ELSE chain.clientHeights[cID] 
                ]
         ] IN
     
    \* update chain with "ClientUpdate" datagrams
    LET updateClients == {dgr \in datagrams : dgr.type = "ClientUpdate"} IN
    LET updateClientIDs == {clientID \in ClientIDs : 
            /\ \E dgr \in updateClients : dgr.clientID = clientID
            /\ ValidClientID(chainID, clientID)} IN
    LET updateClientHeights(clientID) == 
            {h \in Heights : \E dgr \in updateClients : 
                dgr.clientID = clientID /\ dgr.height = h} IN  
    
    \* new chain record with clients updated
    LET clientsUpdated == [
            height |-> clientsCreated.height,
            clientHeights |-> 
                [cID \in ChainIDs |-> IF GetClientID(chainID, cID) \in updateClientIDs
                                      THEN Max(updateClientHeights(GetClientID(chainID, cID)))
                                      ELSE clientsCreated.clientHeights[cID] 
                ]
         ] IN
    
    clientsUpdated
 
\* Update chainID with the received datagrams
\* Currently, only supporting ICS2: Client updates
\* TODO: Support the remaining datagrams
UpdateChain(chainID, datagrams) == 
    LET chain == chains[chainID] IN
    LET lightClientsUpdated == LightClientUpdate(chainID, chain, datagrams) IN 
    
    lightClientsUpdated
    
(***************
Chain actions
***************)       

\* Advance the height of the chain until MaxHeight is reached
AdvanceChain ==
    \E chainID \in ChainIDs :
        /\ chains[chainID].height < MaxHeight
        /\ chains' = [chains EXCEPT 
                        ![chainID].height = chains[chainID].height + 1                                            
                     ]
        /\ UNCHANGED pendingDatagrams

\* Update the height of the light client on chainID for chainID 
UpdateOwnClient ==
    \E chainID \in ChainIDs :
        /\ chains[chainID].clientHeights[chainID] < chains[chainID].height
        /\ chains' = [chains EXCEPT 
                        ![chainID].clientHeights = 
                            [chains[chainID].clientHeights EXCEPT
                                ![chainID] = chains[chainID].height 
                            ]
                     ]
        /\ UNCHANGED pendingDatagrams

\* Receive the datagrams and update the chain state        
ReceiveDatagrams ==
    \E chainID \in ChainIDs :
        /\ pendingDatagrams[chainID] /= {} 
        /\ chains' = [chains EXCEPT 
                        ![chainID] = UpdateChain(chainID, pendingDatagrams[chainID])
                     ]
                        
        /\ pendingDatagrams' = [pendingDatagrams EXCEPT
                                    ![chainID] = {}
                               ]
\* Initial value of the chain: 
\*      - height is initialized to 1
\*      - all the light clients are uninitialized
InitChain ==
    [height |-> 1,
     clientHeights |-> [chID \in ChainIDs |-> nullHeight]]

(***************
Specification
***************)

\* Initial state predicate
\*    Initially
\*        - each chain is initialized to InitChain
\*        - pendingDatagrams for each chain is empty
Init ==    
    /\ chains = [chainID \in ChainIDs |-> InitChain]
    /\ pendingDatagrams = [chainID \in ChainIDs |-> {}]

\* Next state action
\*    Some chain either
\*        - advances its height
\*        - updates the height of its light client
\*        - receives datagrams and updates its state
Next == 
    \/ AdvanceChain
    \/ UpdateOwnClient
    \/ ReceiveDatagrams
    \/ UNCHANGED vars

\* Fairness constraints 
Fairness ==
    /\ WF_vars(AdvanceChain)
    /\ WF_vars(UpdateOwnClient)
    /\ WF_vars(ReceiveDatagrams) 
 
(************
Invariants
************)

\* Type invariant           
TypeOK ==    
    /\ chains \in [ChainIDs -> Chains]
    /\ pendingDatagrams \in [ChainIDs -> SUBSET Datagrams]     

(************
Helper operators used in properties
************)

\* get the set of chainIDs that are different than srcChainID
DstChainIDs(srcChainID) ==
    {chainID \in ChainIDs : chainID /= srcChainID}

\* returns true if there is a "CreateClient" for dstChainID 
\* in the pending datagrams for srcChainID
IsCreateClientInPendingDatagrams(srcChainID, dstChainID) ==
    \E h \in Heights:
        [type |-> "CreateClient", clientID |-> GetClientID(srcChainID, dstChainID), height |-> h] 
            \in pendingDatagrams[srcChainID]

\* returns true if there is a "ClientUpdate" for dstChainID 
\* in the pending datagrams for srcChainID            
IsClientUpdateInPendingDatagrams(srcChainID, dstChainID) ==
    \E h \in Heights:
        [type |-> "ClientUpdate", clientID |-> GetClientID(srcChainID, dstChainID), height |-> h] 
            \in pendingDatagrams[srcChainID]
            

\* returns true if there is a client for dstChainID on srcChainID
IsDstClientOnSrcChain(srcChainID, dstChainID) ==
    chains[srcChainID].clientHeights[dstChainID] /= nullHeight

CurrentClientHeight(srcChainID, dstChainID) ==
    chains[srcChainID].clientHeights[dstChainID]

HeightUpdated(srcChainID, dstChainID, height) ==
    chains[srcChainID].clientHeights[dstChainID] > height

(************
Properties
************)

\* it ALWAYS holds that, for every srcChainID, and every dstChainID:
\*    - if   
\*        * there is a "CreateClient" message for dstChainID
\*          in pending datagrams of srcChainID 
\*        * a client for dstChainID does not exist on srcChainID
\*    - then 
\*        * the client for dstChainID is EVENTUALLY created on srcChainID 
ClientCreated ==
    [](\A srcChainID \in ChainIDs : \A dstChainID \in DstChainIDs(srcChainID) : 
        (/\ IsCreateClientInPendingDatagrams(srcChainID, dstChainID) 
         /\ ~IsDstClientOnSrcChain(srcChainID, dstChainID))
           => (<>(IsDstClientOnSrcChain(srcChainID, dstChainID))))  

\* it ALWAYS holds that, for every srcChainID, and every dstChainID:
\*    - if   
\*        * there is a "ClientUpdate" message for dstChainID
\*          in pending datagrams of srcChainID 
\*        * the height of the client for dstChainID on srcChainID is 
\*          smaller than the height in the update message  
\*    - then 
\*        * the height of the client for dstChainID on srcChainID is EVENTUALLY udpated  
ClientUpdated ==
    [](\A srcChainID \in ChainIDs : \A dstChainID \in DstChainIDs(srcChainID) : \A height \in Heights : 
        (/\ IsClientUpdateInPendingDatagrams(srcChainID, dstChainID) 
         /\ height = CurrentClientHeight(srcChainID, dstChainID))
           => (<>(HeightUpdated(srcChainID, dstChainID, height))))

\* for every chainID, it is always the case that the height of the chain
\* does not decrease                      
HeightsDontDecrease ==
    [](\A chainID \in ChainIDs : \A h \in Heights :
        (chains[chainID].height = h) 
            => <>(chains[chainID].height >= h))                       
                        
=============================================================================
\* Modification History
\* Last modified Tue Mar 17 18:05:50 CET 2020 by ilinastoilkovska
\* Created Fri Mar 13 19:48:22 CET 2020 by ilinastoilkovska
