---------------------------- MODULE ibc_relayer ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NrChains, NrClients, MaxNrConnections, NrChannels, MaxHeight

ASSUME NrClients > NrChains

VARIABLES chains,
          \* a function that assigns to each chainID a chain from the set Chains, where the chainIDs are equal
          clientHeights,
          \* a function that assigns to each clientID a corresponding height
          currentClientID, 
          currentConnectionID
vars == <<chains>>

ChainIDs == 1..NrChains
ClientIDs == 1..NrClients
ChannelIDs == 1..NrChannels
ConnectionIDs == 1..MaxNrConnections
Heights == 1..MaxHeight


ConnectionStates == {"INIT", "TRYOPEN", "OPEN"}

noErr == "no error"
nullClientID == 0


PathEnds ==
    [
        chainID : ChainIDs,
        clientID : ClientIDs,
        connectionID : ConnectionIDs,
        channelID : ChannelIDs
        \* portID
    ]    
    
Paths ==
    [
        src : PathEnds,
        dst : PathEnds 
    ]  
  
(*** ConnectionEnds ***
    A set of functions that maps connection identifiers to connection end records.
    Given a connection identifier connectionID, a connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "INIT", "TRYOPEN", "OPEN".
    
    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the connection end at the counterparty chain which is 
      associated with this connection end.
    
    - clientID -- a client identifier
      Stores the client identifier on this chain associated with this connection end. 
      
    - counterpartyClientID -- a client identifier
      Stores the client identifier of the client at the counterparty chain which is associated with
      this connection end 
**************)    
ConnectionEnds ==
    [ConnectionIDs -> 
        [state : ConnectionStates,
         counterpartyConnectionID : ConnectionIDs,
         clientID : ClientIDs,
         counterpartyClientID : ClientIDs   
        ]
    ]          
    
(*** Chains ***
    A set of functions that maps chain identifiers to chain records.
    Given a chain identifier chainID, a chain record contains the following fields:
    
    - height : an integer between 1 and MaxHeight.
      Stores the current height of the chain
    
    - connectionsEnds : a set of connections ends. 
      This set contains the connection ends to other chains that start in chainID
    
    - clients : a function that assigns a client identifier to a chain identifier
      Given a chain identifier of a counterparty, this function returns the client identifier
      of the light client for the chainID
      
    Each chain has a client that syncs with it and is associated with it.
    This client has the same clientID as the chainID.
**************)
Chains ==    
    [ChainIDs -> 
        [height : Heights,
         connectionEnds : SUBSET(ConnectionEnds), 
         clients : [ChainIDs -> (ClientIDs \cup {nullClientID})]
        ]
    ]
        

Datagrams ==
    [type : {"CreateClient"}, forChainID : ChainIDs, atChainID : ChainIDs]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights] \* abstracting headers with heights
    \union
    [type : {"ConnOpenTry"}]
    \union
    [type : {"ConnOpenAck"}]
    \union
    [type : {"ConnOpenConfirm"}]
    \union 
    [type : {"ChanOpenTry"}]
    \union 
    [type : {"ChanOpenAck"}]
    \union
    [type : {"ChanOpenConfirm"}]
    \union
    [type : {"PacketRecv"}]
    \union
    [type : {"PacketAcknowledgement"}]
 
GetLatestHeight(chainID) ==
    chains[chainID].height
    
QueryClientConsensusState(atChainID, forChainID) ==
    \* the id of the client at atChainID for forChainID
    chains[atChainID].clients[forChainID]
    
SubmitDatagrams(chainID, datagrams) ==
    TRUE
    \* TODO
    
   
 
\* chain (srcChainID) checks whether it should update its client for the counterparty chain (dstChainID) 
LightClientUpdate(srcChainID, dstChainID) ==
    \* height of the counterparty chain
    LET dstChainHeight == GetLatestHeight(dstChainID) IN
    
    \* clientID of the counterparty client:
    \*  - the client that resides at the chain, but which is syncing to the counterparty chain
    LET dstClientIDAtSrcChain == QueryClientConsensusState(srcChainID, dstChainID) IN
    
    \* height of the counterparty client
    LET dstClientHeight == clientHeights[dstClientIDAtSrcChain] IN
    
    IF dstClientIDAtSrcChain = nullClientID
    THEN \* the counterparty client does not exist at the chain 
         {[type |-> "CreateClient", forChain |-> dstChainID, atChain |-> srcChainID]}
    ELSE \* the counterparty chain exists at the chain
         IF dstClientHeight < dstChainHeight
         THEN \* the height of the counterparty client is smaller than the height of the counterparty chain
              {[type |-> "ClientUpdate", forChain |-> dstChainID, atChain |-> srcChainID]}
         ELSE {}
    
CheckConnectionsInProgress(src_chain, dst_chain) ==
    TRUE
    \* TODO
\* return a record [src : msgs, dst : msgs]   

CheckChannelInProgress(src_chain, dst_chain) ==
    TRUE
    \* TODO
\* return a record [src : msgs, dst : msgs]

RelayPacketsAndAcknowledgments(src_chain, dst_chain) ==
    TRUE
    \* TODO
\* return a record [src : msgs, dst : msgs]          
 
\* get client datagrams 
ClientDatagrams(chainID, counterpartyID) ==
    [src |-> LightClientUpdate(chainID, counterpartyID),
     dst |-> LightClientUpdate(counterpartyID, chainID)]

\* get connection datagrams     
ConnectionDatagrams(chainID, counterpartyID) ==
    TRUE
    \* TODO  
 
PendingDatagrams(chainID, counterpartyID) ==
    \* ICS2 : Clients
    \* - Determine if light client needs to be updated (local & counterparty)
    LET clientsDatagrams == ClientDatagrams(chainID, counterpartyID) IN
    \* ICS3 : Connections
    \* - Determine if any connection handshakes are in progress
    LET connectionsDatagrams == ConnectionDatagrams(chainID, counterpartyID) IN
    \* ICS4 : Channels & Packets
    \* - Determine if any channel handshakes are in progress
    LET channelDatagrams == CheckChannelInProgress(chainID, counterpartyID) IN
    \* ICS4 : Channels & Packets
    \* - Determine if any packets, acknowledgements, or timeouts need to be relayed
    LET packetDatagrams == RelayPacketsAndAcknowledgments(chainID, counterpartyID) IN
    
   [src |-> clientsDatagrams.src 
            \union 
            connectionsDatagrams.src 
            \union 
            channelDatagrams.src 
            \union 
            packetDatagrams.src, 
    dst |-> clientsDatagrams.dst 
            \union 
            connectionsDatagrams.dst 
            \union 
            channelDatagrams.dst 
            \union 
            packetDatagrams.dst]
    
    

Init ==
    \* initially, every chain has some height in Heights,
    \* there are no connections,
    \* and no clients that sync with other counterparty chains
    /\ chains = [chainID \in ChainIDs |->
                    [height |-> CHOOSE h \in Heights : TRUE,
                     connectionEnds |-> {},
                     clients |-> 
                        [counterpartyID \in ChainIDs |-> IF counterpartyID = chainID 
                                                         THEN chainID
                                                         ELSE nullClientID]
                    ] 
                ]
    \* intially, all client heights are 0
    /\ clientHeights = [clientID \in ClientIDs |-> 0]
    /\ currentClientID = NrChains + 1
    /\ currentConnectionID = 1
   
     
Next ==
    \E chainID \in DOMAIN chains :
        \E counterpartyID \in DOMAIN chains :
            IF chainID /= counterpartyID
            THEN LET datagrams == PendingDatagrams(chainID, counterpartyID) IN
                 /\ SubmitDatagrams(chainID, datagrams.local)
                 /\ SubmitDatagrams(counterpartyID, datagrams.counterparty)
            ELSE UNCHANGED vars  

ChainHeightClientHeightInvariant ==
    \A chainID \in ChainIDs : 
        clientHeights[chains[chainID].clients[chainID]] <= chains[chainID].height

=============================================================================
\* Modification History
\* Last modified Mon Mar 09 19:56:06 CET 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
