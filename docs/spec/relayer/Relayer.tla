------------------------------ MODULE Relayer ------------------------------

(***************************************************************************
 This module contains the specification of the relayer algorithm. 
 It instantiates the module Environment, which takes care of the chain logic. 
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight \* maximal height of all the chains in the system 

VARIABLES chains, \* a function that assigns a chain record to each chainID 
          outgoingDatagrams, \* a function that assigns a set of pending datagrams 
                             \* outgoing from the relayer to each chainID 
          relayerChainHeights, \* a function that assigns a height to each chainID         
          turn  
          
vars == <<chains, outgoingDatagrams, relayerChainHeights, turn>>
specVars == <<chains, outgoingDatagrams, relayerChainHeights>>             
envVars == <<chains>>           

\* Instance of the module Environment, which encodes the chain logic    
Env == INSTANCE Environment 
       WITH chains <- chains, 
            incomingDatagrams <- outgoingDatagrams,
            MaxHeight <- MaxHeight
                              
ChainIDs == Env!ChainIDs
ClientIDs == Env!ClientIDs
ConnectionIDs == Env!ConnectionIDs
ChannelIDs == Env!ChannelIDs
Heights == Env!Heights
RelayerClientIDs == Env!ClientIDs

nullClientID == Env!nullClientID
nullConnectionID == Env!nullConnectionID
nullHeight == Env!nullHeight

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams == Env!Datagrams
 
(***************************************************************************
 Chain helper operators
 ***************************************************************************) 
\* get the latest height of chainID
GetLatestHeight(chainID) == Env!GetLatestHeight(chainID)

\* get the height of the client for chainID's counterparty chain 
GetMaxCounterpartyClientHeight(chainID) == Env!GetMaxCounterpartyClientHeight(chainID)

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chainID) == Env!GetCounterpartyClientHeights(chainID) 

\* get the ID of chainID's counterparty chain           
GetCounterpartyChainID(chainID) == Env!GetCounterpartyChainID(chainID)

\* get the client ID of the client for chainID     
GetClientID(chainID) == Env!GetClientID(chainID)

\* get the client ID of the client for chainID's counterparty chain
GetCounterpartyClientID(chainID) == Env!GetCounterpartyClientID(chainID)

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chainID) == Env!IsCounterpartyClientOnChain(chainID)

\* returns true if the counterparty client height on chainID is greater or equal than h
CounterpartyClientHeightUpdated(chainID, h) == Env!CounterpartyClientHeightUpdated(chainID, h)

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) == Env!GetConnectionID(chainID)

\* get the connection ID of the connection end at chainID's counterparty chain
GetCounterpartyConnectionID(chainID) == Env!GetCounterpartyConnectionID(chainID)

\* get the connection end at chainID
GetConnectionEnd(chainID) == Env!GetConnectionEnd(chainID)

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chainID) == Env!IsConnectionUninit(chainID)

\* returns true if the connection end on chainID is INIT
IsConnectionInit(chainID) == Env!IsConnectionInit(chainID)

\* returns true if the connection end on chainID is TRYOPEN
IsConnectionTryopen(chainID) == Env!IsConnectionTryopen(chainID)

\* returns true if the connection end on chainID is OPEN
IsConnectionOpen(chainID) == Env!IsConnectionOpen(chainID)

\* get the channel ID of the channel end at the connection end of chainID
GetChannelID(chainID) == Env!GetChannelID(chainID)

\* get the channel ID of the channel end at chainID's counterparty chain
GetCounterpartyChannelID(chainID) == Env!GetCounterpartyChannelID(chainID)

\* get the channel end at the connection end of chainID
GetChannelEnd(chainID) == Env!GetChannelEnd(chainID)

\* returns true if the channel end on chainID is UNINIT
IsChannelUninit(chainID) == Env!IsChannelUninit(chainID)

\* returns true if the channel end on chainID is INIT
IsChannelInit(chainID) == Env!IsChannelInit(chainID)

\* returns true if the channel end on chainID is TRYOPEN
IsChannelTryopen(chainID) == Env!IsChannelTryopen(chainID)

\* returns true if the channel end on chainID is OPEN
IsChannelOpen(chainID) == Env!IsChannelOpen(chainID)

(***************************************************************************
 Client datagrams
 ***************************************************************************)
\* Compute client datagrams designated for dstChainID. 
\* These are used to update the client for srcChainID on dstChainID in the environment.
\* Some client updates might trigger an update of the height that 
\* the relayer stores for srcChainID
LightClientUpdates(srcChainID, dstChainID, relayer) ==
    LET srcChainHeight == GetLatestHeight(srcChainID) IN    
    LET srcClientHeight == GetMaxCounterpartyClientHeight(dstChainID) IN
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
   
(***************************************************************************
 Connection datagrams
 ***************************************************************************)    
\* Compute connection datagrams designated for dstChainID. 
\* These are used to update the connection end on dstChainID in the environment.
ConnectionDatagrams(srcChainID, dstChainID) ==
    LET srcConnectionEnd == GetConnectionEnd(srcChainID) IN
    LET dstConnectionEnd == GetConnectionEnd(dstChainID) IN

    LET srcConnectionID == GetConnectionID(srcChainID) IN
    LET dstConnectionID == GetConnectionID(dstChainID) IN

    LET srcHeight == GetLatestHeight(srcChainID) IN
    LET srcConsensusHeight == GetMaxCounterpartyClientHeight(srcChainID) IN
    
    IF dstConnectionEnd.state = "UNINIT" /\ srcConnectionEnd.state = "UNINIT" THEN 
         {[type |-> "ConnOpenInit", 
           connectionID |-> dstConnectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           clientID |-> GetCounterpartyClientID(dstChainID), \* "clA"
           counterpartyConnectionID |-> srcConnectionID, \* "connAtoB"
           counterpartyClientID |-> GetCounterpartyClientID(srcChainID)]} \* "clB" 
    
    ELSE IF srcConnectionEnd.state = "INIT" /\ \/ dstConnectionEnd.state = "UNINIT"
                                               \/ dstConnectionEnd.state = "INIT" THEN 
         {[type |-> "ConnOpenTry",
           desiredConnectionID |-> dstConnectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           clientID |-> srcConnectionEnd.counterpartyClientID, \* "clA"
           counterpartyConnectionID |-> srcConnectionID, \* "connAtoB"
           counterpartyClientID |-> srcConnectionEnd.clientID, \* "clB" 
           proofHeight |-> srcHeight,
           consensusHeight |-> srcConsensusHeight]}
         
    ELSE IF srcConnectionEnd.state = "TRYOPEN" /\ \/ dstConnectionEnd.state = "INIT"
                                                  \/ dstConnectionEnd.state = "TRYOPEN" THEN
         {[type |-> "ConnOpenAck",
           connectionID |-> dstConnectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight,
           consensusHeight |-> srcConsensusHeight]} 
         
    ELSE IF srcConnectionEnd.state = "OPEN" /\ dstConnectionEnd.state = "TRYOPEN" THEN
         {[type |-> "ConnOpenConfirm",
           connectionID |-> dstConnectionEnd.connectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight]} 
    ELSE {}

(***************************************************************************
 Channel datagrams
 ***************************************************************************)
\* Compute channel datagrams designated for dstChainID. 
\* These are used to update the channel end on dstChainID in the environment.
ChannelDatagrams(srcChainID, dstChainID) ==
    LET srcChannelEnd == GetChannelEnd(srcChainID) IN
    LET dstChannelEnd == GetChannelEnd(dstChainID) IN
    
    LET srcChannelID == GetChannelID(srcChainID) IN
    LET dstChannelID == GetChannelID(dstChainID) IN

    LET srcHeight == GetLatestHeight(srcChainID) IN
    
    IF dstChannelEnd.state = "UNINIT" /\ srcChannelEnd.state = "UNINIT" THEN 
         {[type |-> "ChanOpenInit", 
           channelID |-> dstChannelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           counterpartyChannelID |-> srcChannelID]} \* "chanAtoB" 
    
    ELSE IF srcChannelEnd.state = "INIT" /\ \/ dstChannelEnd.state = "UNINIT"
                                            \/ dstChannelEnd.state = "INIT" THEN 
         {[type |-> "ChanOpenTry",
           channelID |-> dstChannelID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           counterpartyChannelID |-> srcChannelID, \* "chanAtoB"
           proofHeight |-> srcHeight]} 
         
    ELSE IF srcChannelEnd.state = "TRYOPEN" /\ \/ dstChannelEnd.state = "INIT"
                                               \/ dstChannelEnd.state = "TRYOPEN" THEN
         {[type |-> "ChanOpenAck",
           channelID |-> dstChannelID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight]} 
         
    ELSE IF srcChannelEnd.state = "OPEN" /\ dstChannelEnd.state = "TRYOPEN" THEN
         {[type |-> "ChanOpenConfirm",
           channelID |-> dstChannelEnd.channelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight]} 
    ELSE {}
    
(***************************************************************************
 Compute pending datagrams (from srcChainID to dstChainID)
 ***************************************************************************)
\* Currently supporting:
\*  -  ICS 002: Client updates
\*  -  ICS 003: Connection handshake
\*  -  ICS 004: Channel handshake
\* TODO: Support the remaining datagrams
PendingDatagrams(srcChainID, dstChainID) ==
    \* ICS 002 : Clients
    \* - Determine if light clients needs to be updated 
    LET clientDatagrams == LightClientUpdates(srcChainID, dstChainID, relayerChainHeights) IN
    
    \* ICS3 : Connections
    \* - Determine if any connection handshakes are in progress
    LET connectionDatagrams == ConnectionDatagrams(srcChainID, dstChainID) IN
    
    \* ICS4 : Channels & Packets
    \* - Determine if any channel handshakes are in progress
    LET channelDatagrams == ChannelDatagrams(srcChainID, dstChainID) IN
    
    \* ICS4 : Channels & Packets
    \* - Determine if any packets, acknowledgements, or timeouts need to be relayed
    \* TODO
    
    [datagrams |-> clientDatagrams.datagrams \union 
                   connectionDatagrams \union 
                   channelDatagrams, 
     relayerUpdate |-> clientDatagrams.relayerUpdate]

(***************************************************************************
 Relayer actions
 ***************************************************************************)   
\* Update the height of the relayer client for some chainID
UpdateRelayerClients(chainID) ==
        /\ relayerChainHeights[chainID] < GetLatestHeight(chainID)
        /\ relayerChainHeights' = [relayerChainHeights EXCEPT 
                                        ![chainID] = GetLatestHeight(chainID)
                                   ]
        /\ UNCHANGED <<chains, outgoingDatagrams>>  

\* for two chains, srcChainID and dstChainID, where srcChainID /= dstChainID, 
\* create the pending datagrams and update the corresponding sets of pending datagrams
Relay(srcChainID, dstChainID) ==
    LET datagramsAndRelayerUpdate == PendingDatagrams(srcChainID, dstChainID) IN
    /\ srcChainID /= dstChainID
    /\ outgoingDatagrams' = 
            [outgoingDatagrams EXCEPT 
                ![dstChainID] = outgoingDatagrams[dstChainID] 
                                \union 
                                datagramsAndRelayerUpdate.datagrams
            ]
    /\ relayerChainHeights' = datagramsAndRelayerUpdate.relayerUpdate       
    /\ UNCHANGED chains

(***************************************************************************
 Component actions
 ***************************************************************************)
\* Relayer
\*    The relayer either
\*        - updates its clients, or
\*        - relays datagrams between two chains, or
\*        - does nothing
Relayer ==
    \/ \E chainID \in ChainIDs : UpdateRelayerClients(chainID)
    \/ \E srcChainID \in ChainIDs : \E dstChainID \in ChainIDs : Relay(srcChainID, dstChainID)
    \/ UNCHANGED vars
    
\* Environment
\*    The environment takes the action Env!Next
\*    and leaves the relayer variable unchanged
Environment ==
    /\ Env!Next
    /\ UNCHANGED relayerChainHeights    

(***************************************************************************
 Specification
 ***************************************************************************)
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
    /\ \A chainID \in ChainIDs : 
            WF_specVars(UpdateRelayerClients(chainID))
    /\ \A srcChainID \in ChainIDs : \A dstChainID \in ChainIDs : 
            WF_specVars(Relay(srcChainID, dstChainID))
    /\ Env!Fairness 
                        
\* Spec formula
Spec == Init /\ [][Next]_vars /\ Fairness   

(***************************************************************************
 Helper operators used in properties
 ***************************************************************************)
\* returns true if there is a "CreateClient" datagram
\* in outgoing datagrams for chainID 
IsCreateClientInPendingDatagrams(chainID, clID, h) == 
    [type |-> "CreateClient", clientID |-> clID, height |-> h] 
        \in outgoingDatagrams[chainID]

\* returns true if there is a "ClientUpdate" datagram
\* in outgoing datagrams for chainID           
IsClientUpdateInPendingDatagrams(chainID, clID, h) ==
    [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
        \in outgoingDatagrams[chainID]

\* returns true if there is a "ConnOpenInit" datagram  
\* for the connection between srcChainID and dstChainID
ConnOpenInitGenerated(srcChainID, dstChainID) == 
    LET srcClientID == GetClientID(dstChainID) IN
    LET dstClientID == GetClientID(srcChainID) IN
    LET srcConnectionID == GetConnectionID(srcChainID) IN
    LET dstConnectionID == GetConnectionID(dstChainID) IN
    
    [type |-> "ConnOpenInit", 
        connectionID |-> srcConnectionID, 
        clientID |-> srcClientID,
        counterpartyConnectionID |-> dstConnectionID,
        counterpartyClientID |-> dstClientID] \in outgoingDatagrams[srcChainID]

\* returns true if there is a "ConnOpenInit" datagram 
\* in outgoing datagrams for chainID                
IsConnOpenInitInPendingDatagrams(
    chainID, clientID, counterpartyClientID,
    connectionID, counterpartyConnectionID
    ) ==     
    
    [type |-> "ConnOpenInit", 
     connectionID |-> connectionID, 
     clientID |-> clientID,
     counterpartyConnectionID |-> counterpartyConnectionID,
     counterpartyClientID |-> counterpartyClientID] \in outgoingDatagrams[chainID]
    
\* returns true if there is a "ConnOpenTry" datagram 
\* in outgoing datagrams for chainID
IsConnOpenTryInPendingDatagrams(
    chainID, clientID, counterpartyClientID,
    connectionID, counterpartyConnectionID
    ) ==
    
    \E pHeight \in Heights : \E cHeight \in Heights :
    [type |-> "ConnOpenTry", 
     desiredConnectionID |-> connectionID, 
     clientID |-> clientID,
     counterpartyConnectionID |-> counterpartyConnectionID,
     counterpartyClientID |-> counterpartyClientID,
     proofHeight |-> pHeight,
     consensusHeight |-> cHeight] \in outgoingDatagrams[chainID]

\* returns true if there is a "ConnOpenAck" datagram
\* in outgoing datagrams for chainID
IsConnOpenAckInPendingDatagrams(chainID, connectionID) ==
    \E pHeight \in Heights : \E cHeight \in Heights :
    [type |-> "ConnOpenAck", 
     connectionID |-> connectionID, 
     proofHeight |-> pHeight,
     consensusHeight |-> cHeight] \in outgoingDatagrams[chainID]

\* returns true if there is a "ConnOpenConfirm" datagram 
\* in outgoing datagrams for chainID
IsConnOpenConfirmInPendingDatagrams(chainID, connectionID) ==
    \E pHeight \in Heights : 
    [type |-> "ConnOpenConfirm", 
     connectionID |-> connectionID, 
     proofHeight |-> pHeight] \in outgoingDatagrams[chainID]

\* returns true if there is a "ChanOpenInit" datagram  
\* in outgoing datagrams for chainID
IsChanOpenInitInPendingDatagrams(chainID, channelID, counterpartyChannelID) ==
    [type |-> "ChanOpenInit", 
     channelID |-> channelID, 
     counterpartyChannelID |-> counterpartyChannelID] \in outgoingDatagrams[chainID]

\* returns true if there is a "ChanOpenTry" datagram 
\* in outgoing datagrams for chainID
IsChanOpenTryInPendingDatagrams(chainID, channelID, counterpartyChannelID) ==
    \E pHeight \in Heights :
    [type |-> "ChanOpenTry", 
     channelID |-> channelID, 
     counterpartyChannelID |-> counterpartyChannelID,
     proofHeight |-> pHeight] \in outgoingDatagrams[chainID]

\* returns true if there is a "ChanOpenAck" datagram
\* in outgoing datagrams for chainID
IsChanOpenAckInPendingDatagrams(chainID, channelID) ==
    \E pHeight \in Heights :
    [type |-> "ChanOpenAck", 
     channelID |-> channelID, 
     proofHeight |-> pHeight] \in outgoingDatagrams[chainID]

\* returns true if there is a "ChanOpenConfirm" datagram 
\* in outgoing datagrams for chainID
IsChanOpenConfirmInPendingDatagrams(chainID, channelID) ==
    \E pHeight \in Heights : 
    [type |-> "ChanOpenConfirm", 
     channelID |-> channelID, 
     proofHeight |-> pHeight] \in outgoingDatagrams[chainID]     

(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant
TypeOK ==
    /\ turn \in {"relayer", "environment"}
    /\ relayerChainHeights \in [ChainIDs -> Heights \union {nullHeight}]
    /\ Env!TypeOK
    
\* CreateClientInv   
\* if a "CreateClient" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID 
\* and the client that should be created does not exist (has null height)
CreateClientInv ==
    \A chainID \in ChainIDs : \A clID \in ClientIDs :  
        ((\E h \in Heights : IsCreateClientInPendingDatagrams(chainID, clID, h)) 
            => (/\ clID = GetCounterpartyClientID(chainID)
                /\ GetCounterpartyClientHeights(chainID) = {}))

\* if a "ClientUpdate" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID   
\* and the client that should be updated has height less than the one in the datagram
ClientUpdateInv ==
    \A chainID \in ChainIDs : \A clID \in ClientIDs : \A h \in Heights :
        IsClientUpdateInPendingDatagrams(chainID, clID, h) 
            => (/\ clID = GetCounterpartyClientID(chainID)
                /\ GetMaxCounterpartyClientHeight(chainID) < h)

\* ConnOpenInitInv   
\* if a "ConnOpenInit" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID, counterparty clientID,
\* connection ID, counterparty connection ID
\* and the connection that should be in INIT is currently in UNINIT
ConnOpenInitInv ==
    \A chainID \in ChainIDs :
    \A clientID \in ClientIDs : \A counterpartyClientID \in ClientIDs :
    \A connectionID \in ConnectionIDs : \A counterpartyConnectionID \in ConnectionIDs :
        IsConnOpenInitInPendingDatagrams(chainID, clientID, counterpartyClientID, 
                                         connectionID, counterpartyConnectionID)
            => /\ clientID = GetCounterpartyClientID(chainID)
               /\ counterpartyClientID = GetClientID(chainID)
               /\ connectionID = GetConnectionID(chainID)
               /\ counterpartyConnectionID = GetCounterpartyConnectionID(chainID)
               /\ IsConnectionUninit(chainID)
        

\* ConnOpenTryInv   
\* if a "ConnOpenTry" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID, counterparty clientID,
\* connection ID, counterparty connection ID, proof height, consensus height
\* and the connection that should be in TRYOPEN is currently either UNINIT or INIT
ConnOpenTryInv ==
    \A chainID \in ChainIDs :
    \A clientID \in ClientIDs : \A counterpartyClientID \in ClientIDs :
    \A connectionID \in ConnectionIDs : \A counterpartyConnectionID \in ConnectionIDs :
        IsConnOpenTryInPendingDatagrams(
            chainID, clientID, counterpartyClientID,
            connectionID, counterpartyConnectionID
        )
            => /\ clientID = GetCounterpartyClientID(chainID)
               /\ counterpartyClientID = GetClientID(chainID)
               /\ connectionID = GetConnectionID(chainID)
               /\ counterpartyConnectionID = GetCounterpartyConnectionID(chainID)
               /\ \/ IsConnectionUninit(chainID)
                  \/ IsConnectionInit(chainID)

\* ConnOpenAckInv   
\* if a "ConnOpenAck" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct connection ID, proof height, consensus height
\* and the connection that should be in OPEN is currently either INIT or TRYOPEN
ConnOpenAckInv ==
    \A chainID \in ChainIDs : \A connectionID \in ConnectionIDs : 
        IsConnOpenAckInPendingDatagrams(chainID, connectionID)
            => /\ connectionID = GetConnectionID(chainID)
               /\ \/ IsConnectionInit(chainID)
                  \/ IsConnectionTryopen(chainID)
    
\* ConnOpenConfirmInv   
\* if a "ConnOpenConfirm" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID, counterparty clientID,
\* connection ID, counterparty connection ID, proof height
\* and the connection that should be in OPEN is currently TRYOPEN
ConnOpenConfirmInv ==
    \A chainID \in ChainIDs : \A connectionID \in ConnectionIDs : 
        IsConnOpenConfirmInPendingDatagrams(chainID, connectionID)
            => /\ connectionID = GetConnectionID(chainID)
               /\ IsConnectionTryopen(chainID)
               
\* ChanOpenInitInv   
\* if a "ChanOpenInit" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID, counterparty clientID,
\* connection ID, counterparty connection ID
\* and the connection that should be in INIT is currently in UNINIT
ChanOpenInitInv ==
    \A chainID \in ChainIDs : 
    \A channelID \in ChannelIDs : \A counterpartyChannelID \in ChannelIDs :
        IsChanOpenInitInPendingDatagrams(chainID, channelID, counterpartyChannelID)
            => /\ channelID = GetChannelID(chainID)
               /\ counterpartyChannelID = GetCounterpartyChannelID(chainID)
               /\ IsChannelUninit(chainID)
        

\* ChanOpenTryInv   
\* if a "ChanOpenTry" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID, counterparty clientID,
\* connection ID, counterparty connection ID, proof height, consensus height
\* and the connection that should be in TRYOPEN is currently either UNINIT or INIT
ChanOpenTryInv ==
    \A chainID \in ChainIDs : 
    \A channelID \in ChannelIDs : \A counterpartyChannelID \in ChannelIDs :
        IsChanOpenTryInPendingDatagrams(chainID, channelID, counterpartyChannelID)
            => /\ channelID = GetChannelID(chainID)
               /\ counterpartyChannelID = GetCounterpartyChannelID(chainID)
               /\ \/ IsChannelUninit(chainID)
                  \/ IsChannelInit(chainID)

\* ChanOpenAckInv   
\* if a "ChanOpenAck" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct connection ID, proof height, consensus height
\* and the connection that should be in OPEN is currently either INIT or TRYOPEN
ChanOpenAckInv ==
    \A chainID \in ChainIDs : \A channelID \in ChannelIDs :
        IsChanOpenAckInPendingDatagrams(chainID, channelID)
            => /\ \/ IsChannelInit(chainID)
                  \/ IsChannelTryopen(chainID)
    
\* ChanOpenConfirmInv   
\* if a "ChanOpenConfirm" datagram is in pendingDatagrams for chainID, 
\* then the datagram has the correct client ID, counterparty clientID,
\* connection ID, counterparty connection ID, proof height
\* and the connection that should be in OPEN is currently TRYOPEN
ChanOpenConfirmInv ==
    \A chainID \in ChainIDs : \A channelID \in ChannelIDs : 
        IsChanOpenConfirmInPendingDatagrams(chainID, channelID)
            => /\ IsChannelTryopen(chainID)               

\* Inv
\* A conjunction of all invariants                            
Inv ==
    /\ TypeOK
    /\ CreateClientInv
    /\ ClientUpdateInv
    /\ ConnOpenInitInv
    /\ ConnOpenTryInv
    /\ ConnOpenAckInv
    /\ ConnOpenConfirmInv
    /\ ChanOpenInitInv
    /\ ChanOpenTryInv
    /\ ChanOpenAckInv
    /\ ChanOpenConfirmInv

(***************************************************************************
 Properties about client updates
 ***************************************************************************)
\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the counterparty client is not initialized
\*  - then
\*      * the relayer EVENTUALLY adds a "CreateClient" datagram in pending datagrams of chainID
CreateClientIsGenerated == 
    [](\A chainID \in ChainIDs : 
        GetCounterpartyClientHeights(chainID) = {}
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
        (/\ GetMaxCounterpartyClientHeight(chainID) = h1
         /\ GetMaxCounterpartyClientHeight(chainID) < GetLatestHeight(GetCounterpartyChainID(chainID)))
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
         /\ GetMaxCounterpartyClientHeight(chainID) < h)
           => (<>(CounterpartyClientHeightUpdated(chainID, h))))
    
(***************************************************************************
 Properties about connection handshake
 ***************************************************************************)           
\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the connection on chainID is uninitialized and 
\*      * the connection on chainID's counterparty is uninitialized
\*  - then EVENTUALLY either
\*      * there is a "ConnOpenInit" datagram in pending datagrams of chainID  
\*      * or the state of the counterparty connection is "INIT"         
ConnOpenInitIsGenerated ==
    [](\A chainID \in ChainIDs : 
         IsConnectionUninit(chainID)
            => <>(\/ IsConnOpenInitInPendingDatagrams(
                        chainID, GetCounterpartyClientID(chainID), GetClientID(chainID), 
                        GetConnectionID(chainID), GetCounterpartyConnectionID(chainID)
                     )
                  \/ IsConnectionInit(GetCounterpartyChainID(chainID))))
          
\* it ALWAYS holds that, for every cahinID, and every counterpartyChainID:
\*    - if   
\*        * there is a "ConnOpenInit" datagram in pending datagrams of chainID 
\*        * the connection is not open  
\*    - then 
\*        * the connection is EVENTUALLY open              
ConnectionOpened ==
    [](\A chainID \in ChainIDs : 
        IsConnOpenInitInPendingDatagrams(
               chainID, GetClientID(chainID), GetCounterpartyClientID(chainID),
               GetConnectionID(chainID), GetCounterpartyConnectionID(chainID)
        )
            => <>(/\ IsConnectionOpen(chainID)
                  /\ IsConnectionOpen(GetCounterpartyChainID(chainID))))              

(***************************************************************************
 Properties about channel handshake
 ***************************************************************************)           
\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the chain on chainID is uninitialized and 
\*      * the chain on chainID's counterparty is uninitialized
\*  - then
\*      * the relayer EVENTUALLY adds a "ChanOpenInit" datagram in pending datagrams of chainID           
ChanOpenInitIsGenerated ==
    [](\A chainID \in ChainIDs : 
        (IsChannelUninit(chainID)
            => <>(\/ IsChanOpenInitInPendingDatagrams(chainID, GetChannelID(chainID), GetCounterpartyChannelID(chainID))
                  \/ IsChannelInit(GetCounterpartyChainID(chainID)))))
          
\* it ALWAYS holds that, for every cahinID, and every counterpartyChainID:
\*    - if   
\*        * there is a "ChanOpenInit" datagram in pending datagrams of chainID 
\*    - then 
\*        * the channel is EVENTUALLY open              
ChannelOpened ==
    [](\A chainID \in ChainIDs :
        IsChanOpenInitInPendingDatagrams(chainID, GetChannelID(chainID), GetCounterpartyChannelID(chainID))
            => <>(/\ IsChannelOpen(chainID)
                  /\ IsChannelOpen(GetCounterpartyChainID(chainID))))              


(***************************************************************************
 Properties about the environment
 ***************************************************************************) 
\* for every chainID, it is always the case that the height of the chain
\* does not decrease                      
HeightsDontDecrease ==
    [](\A chainID \in ChainIDs : \A h \in Heights :
        (chains[chainID].height = h) 
            => <>(chains[chainID].height >= h))           

\* Prop
\* A conjunction of all properties                                                             
Prop ==                           
    /\ CreateClientIsGenerated 
    /\ ClientCreated 
    /\ ClientUpdateIsGenerated 
    /\ ClientUpdated 
    /\ ConnOpenInitIsGenerated
    /\ ConnectionOpened 
    /\ ChanOpenInitIsGenerated
    /\ ChannelOpened
    /\ HeightsDontDecrease 

=============================================================================
\* Modification History
\* Last modified Tue May 26 12:13:36 CEST 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
