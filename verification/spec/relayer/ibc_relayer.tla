---------------------------- MODULE ibc_relayer ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NrChains, NrClients, NrConnectionsPerChain, NrChannelsPerConnection, MaxHeight

ASSUME NrClients > NrChains

VARIABLES chains, \* a function that assigns to each chainID a chain record
          clientHeights, \* a function that assigns to each clientID a corresponding height
          connectionEnds, \* a function that assigns to every connectionID a connection end record
          channelEnds \* a function that assigns to every channelID a channel end record
          
vars == <<chains, clientHeights, connectionEnds, channelEnds>>

ChainIDs == 1..NrChains
ClientIDs == 1..NrClients
ConnectionIDs == 1..(NrConnectionsPerChain * NrChains)
ChannelIDs == 1..(NrChannelsPerConnection * NrConnectionsPerChain * NrChains)
Heights == 1..MaxHeight


ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}
ChannelOrder == {"ORDERED", "UNORDERED"}

noErr == "no error"
nullClientID == 0
nullHeight == 0
nullConnectionID == 0
nullChannelID == 0
nullConnectionEnd == [state |-> "UNINIT", counterpartyConnectionID |-> nullConnectionID, 
                      clientID |-> nullClientID, counterpartyClientID |-> nullClientID] 
nullChannelEnds == [state : {"UNINIT"}, ordering : ChannelOrder, counterpartyChannelID : {nullChannelID}]                     

(*** ConnectionEnds ***
    A set of connection end records. 
    A connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".
    
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
    [
        state : ConnectionStates,
        counterpartyConnectionID : ConnectionIDs,
        clientID : ClientIDs,
        counterpartyClientID : ClientIDs   
    ] 
       
(*** ChannelEnds ***
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED".
    
    - ordering -- a string 
      Stores whether the channel is "ORDERED" or "UNORDERED"
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the channel end at the counterparty chain which is 
      associated with this channel end. 
**************)       
ChannelEnds ==
    [
        state : ChannelStates, 
        ordering : ChannelOrder,
        counterpartyChannelID : ChannelIDs
    ]       
                 
    
(*** Chains ***
    A set of chain records. 
    A chain record contains the following fields:
    
    - height : an integer between 1 and MaxHeight. 
      Stores the current height of the chain.
    
    - clients : a function that maps chain identifiers to client identifier.
      Given a chain identifier of a counterparty, this function returns the client identifier
     
**************)
Chains ==    
    [
        height : Heights,
        clients : [ChainIDs -> (ClientIDs \cup {nullClientID})]
    ]
    
\*    
\*Connections ==
\*    [ConnectionIDs -> ConnectionEnds]    
        

Datagrams ==
    [type : {"CreateClient"}, forChainID : ChainIDs, atChainID : ChainIDs]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights] 
    \union
    [type : {"ConnOpenInit"}, connID : ConnectionIDs, clientID : ClientIDs]
    \union
    [type : {"ConnOpenTry"}, desiredConnID : ConnectionIDs, counterpartyConnID : ConnectionIDs, 
     counterparyClientID : ClientIDs, clientID : ClientIDs, proofHeight : Heights, consensusHeight : Heights]
    \union
    [type : {"ConnOpenAck"}, connID : ConnectionIDs, proofHeight : Heights, consensusHeight : Heights ]
    \union
    [type : {"ConnOpenConfirm"}, connID : ConnectionIDs, proofHeight : Heights]
    \union 
    [type : {"ChanOpenInit"}] \* fields? 
    \union 
    [type : {"ChanOpenTry"}, order : ChannelOrder, chanID : ChannelIDs, counterpartyChanID : ChannelIDs, proofHeight : Heights]
    \union 
    [type : {"ChanOpenAck"}, chanID : ChannelIDs, proofHeight : Heights]
    \union
    [type : {"ChanOpenConfirm"}, chanID : ChannelIDs, proofHeight : Heights]
    \union
    [type : {"PacketRecv"}]
    \union
    [type : {"PacketAcknowledgement"}]
 
\* Get the set of ConnectionIDs associated with the chainID
GetChainConnectionIDs(chainID) ==
    \* assume that there are NrConnectionsPerChain for each chainID
    {chainID * i : i \in 1..NrConnectionsPerChain}

\* Get the set of ChannelIDs associated with the connectionID
GetConnectionEndChannelIDs(connectionID) ==
    \* assume that there are NrChannelsPerConnection for each connectionID
    {connectionID * i : i \in 1..NrChannelsPerConnection}
    
 
(***************
Client datagrams
****************) 
 
\* get the latest height of the chainID
GetLatestHeight(chainID) ==
    chains[chainID].height
  
\* get the clientID of the client at chain atChainID for chain forChainID    
QueryClientID(atChainID, forChainID) ==
    chains[atChainID].clients[forChainID]
     
\* chain (srcChainID) checks whether it should update its client 
\* for the counterparty chain (dstChainID) 
LightClientUpdate(srcChainID, dstChainID) ==
    \* height of the counterparty chain
    LET dstChainHeight == GetLatestHeight(dstChainID) IN
    
    \* clientID of the counterparty client:
    \*  - the client that resides at the chain, but which is syncing to the counterparty chain
    LET dstClientIDAtSrcChain == QueryClientID(srcChainID, dstChainID) IN
    
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
    
\* get client datagrams 
ClientDatagrams(chainID, counterpartyID) ==
    [src |-> LightClientUpdate(chainID, counterpartyID),
     dst |-> LightClientUpdate(counterpartyID, chainID)]    
    
(*******************
Connection datagrams
*******************)

\* get connection IDs of connections between chainID and counterpartyID 
GetConnectionIDs(chainID, counterpartyID) == 
    LET counterpartyConnectionID(connectionID) ==
        connectionEnds[connectionID].counterpartyConnectionID IN
    LET counterpartyClientIDAtChain(connectionID) ==
        connectionEnds[connectionID].counterpartyClientID IN
    LET chainClientIDAtCounterparty(connectionID) == 
        connectionEnds[counterpartyConnectionID(connectionID)].clientID IN
    
    \* get the connectionIDs in the store of chainID, where the counterparty clientIDs coincide
    {connectionID \in GetChainConnectionIDs(chainID) : 
        counterpartyClientIDAtChain(connectionID) = 
            chainClientIDAtCounterparty(connectionID)}
  
\* get connection datagrams for a given connectionID local to chainID, which connects to counterpartyID
GetConnectionDatagrams(chainID, counterpartyID, connectionID) == 
    LET localEnd == connectionEnds[connectionID] IN
    LET remoteEnd == connectionEnds[localEnd.counterpartyConnectionID] IN
    LET height == chains[chainID].height IN
    LET localConsensusHeight == clientHeights[localEnd.clientID] IN
    LET remoteConsensusHeight == clientHeights[remoteEnd.clientID] IN
    
    IF localEnd.state = "UNINIT" /\ remoteEnd.state = "UNINIT"
    THEN [src |-> {[type |-> "ConnOpenInit", 
                    connID |-> connectionID, 
                    clientID |-> localEnd.clientID]}, 
          dst |-> {}]
    ELSE IF localEnd.state = "INIT" /\ remoteEnd.state = "UNINIT"
         THEN [src |-> {}, 
               dst |-> {[type |-> "ConnOpenTry",
                         desiredConnID |-> localEnd.counterpartyConnectionID, 
                         counterpartyConnID |-> connectionID,
                         counterpartyClientID |-> localEnd.clientID, 
                         clientID |-> localEnd.counterpartyClientID, 
                         proofHeight |-> height,
                         consensusHeight |->  localConsensusHeight]}] 
         ELSE IF localEnd.state = "INIT" /\ remoteEnd.state = "TRYOPEN"
              THEN [src |-> {[type |-> "ConnOpenAck",
                              connID |-> connectionID,
                              proofHeight |-> remoteConsensusHeight,
                              consensusHeight |-> remoteConsensusHeight]}, 
                    dst |-> {}] 
              ELSE IF localEnd.state = "OPEN" /\ remoteEnd.state = "TRYOPEN"
                   THEN [src |-> {}, 
                         dst |-> {[type |-> "ConnOpenConfirm",
                                   connID |-> localEnd.counterpartyConnectionID, \* using this instead of remoteEnd.connectionID
                                   proofHeight |-> height]}] 
                   ELSE [src |-> {}, dst |-> {}]

\* get connection datagrams     
ConnectionDatagrams(chainID, counterpartyID) ==
    LET connectionIDs == GetConnectionIDs(chainID, counterpartyID) IN
    
    [src |-> UNION {GetConnectionDatagrams(chainID, counterpartyID, connectionID).src 
                                                        : connectionID \in connectionIDs},
     dst |-> UNION {GetConnectionDatagrams(chainID, counterpartyID, connectionID).dst 
                                                        : connectionID \in connectionIDs}]
  

(****************
Channel datagrams
****************)

GetChannelIDs(chainID, counterpartyID) ==
    LET connectionIDs == GetConnectionIDs(chainID, counterpartyID) IN

    UNION {GetConnectionEndChannelIDs(connectionID) : connectionID \in connectionIDs}

GetChannelDatagrams(chainID, counterpartyID, channelID) ==
    LET localEnd == channelEnds[channelID] IN
    LET remoteEnd == channelEnds[localEnd.counterpartyChannelID] IN
    LET height == chains[chainID].height IN
    LET localClientHeight == clientHeights[localEnd.clientID] IN
    
    IF localEnd.state = "UNINIT" /\ remoteEnd.state = "UNINIT"
    THEN [src |-> {[type |-> "ChanOpenInit"]},  \* fields? 
          dst |-> {}]
    ELSE IF localEnd.state = "INIT" /\ remoteEnd.state = "UNINIT"
         THEN [src |-> {},
               dst |-> {[type |-> "ChanOpenTry",
                         order |-> localEnd.order,
                         chanID |-> localEnd.counterpartyChannelID, 
                         counterpartyChanID |-> localEnd.channelID,
                         proofHeight |-> height]}]
         ELSE IF localEnd.state = "INIT" /\ remoteEnd.state = "TRYOPEN"
              THEN [src |-> {[type |-> "ChanOpenAck",
                              chanID |-> channelID,
                              proofHeight |-> localClientHeight]},              
                    dst |-> {}] 
              ELSE IF localEnd.state = "OPEN" /\ remoteEnd.state = "TRYOPEN"
                   THEN [src |-> {},
                         dst |-> {[type |-> "ChanOpenConfirm",
                                   chanID |-> localEnd.counterpartyChannelID, \* using this instead of remoteEnd.channelID
                                   proofHeight |-> height]}] 
                   ELSE [src |-> {}, dst |-> {}] 

ChannelDatagrams(chainID, counterpartyID) ==
    LET channelIDs == GetChannelIDs(chainID, counterpartyID) IN
    
    [src |-> UNION {GetChannelDatagrams(chainID, counterpartyID, channelID).src 
                                                        : channelID \in channelIDs},
     dst |-> UNION {GetChannelDatagrams(chainID, counterpartyID, channelID).dst 
                                                        : channelID \in channelIDs}]


\* PacketDatagram relies on querying logs. 
\* How to model this in TLA+?
PacketDatagrams(src_chain, dst_chain) ==
    TRUE
    \* TODO
\* return a record [src : msgs, dst : msgs]          

    
    
 
PendingDatagrams(chainID, counterpartyID) ==
    \* ICS2 : Clients
    \* - Determine if light client needs to be updated (local & counterparty)
    LET clientsDatagrams == ClientDatagrams(chainID, counterpartyID) IN
    \* ICS3 : Connections
    \* - Determine if any connection handshakes are in progress
    LET connectionsDatagrams == ConnectionDatagrams(chainID, counterpartyID) IN
    \* ICS4 : Channels & Packets
    \* - Determine if any channel handshakes are in progress
    LET channelDatagrams == ChannelDatagrams(chainID, counterpartyID) IN
    \* ICS4 : Channels & Packets
    \* - Determine if any packets, acknowledgements, or timeouts need to be relayed
    LET packetDatagrams == PacketDatagrams(chainID, counterpartyID) IN
    
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
 

SubmitDatagrams(chainID, datagrams) ==
    TRUE
    \* TODO

(**********    
Relayer specification

Variables:
    - chains: a function from ChainIDs to chain records.
      Each chain record has the following fields:
        * height -- an integer between 1 and MaxHeight. Stores the current height of the chain.
          Initially chosen non-deterministically.
          
        * clients -- a function that maps ChainIDs to ClientIDs. 
          E.g., chains[chainID].clients[counterpartyID] is the client identifier of 
          the client for the chain counterpartyID that is found in chainID's store.
          
          Initially:
            - If chainID /= counterpartyID, then chains[chainID].clients[counterpartyID] is 
              set to nullClientID, meaning that the client for counterpartyID does not exist 
              in chainID's store yet.
            - If chainID = counterpartyID, then chains[chainID].clients[counterpartyID] is 
              set to chainID, meaning that the client for chainID has the same id as the chain
              it is associated to.
                    
    - clientHeights: a function from ClientIDs to Heights. Stores the current height of each 
      clientID \in ClientIDs. Initially, clientHeights[clientID] is set to nullHeight (== 0).

    - connectionEnds: a function from ConnectionIDs to connection end records.
      Initially, connectionEnds[connectionID] is set to nullConnectionEnd (where the state is "UNINIT")
    
    - channelEnds: a function from ChannelIDs to channel end records     
      Initially, channelEnds[channelID] is set to nullChannelEnd (where the state is "UNINIT")
**********)   

Init ==
    /\ chains = [ChainIDs -> Chains]
    /\ \A chainID \in ChainIDs :
            \* the clientID for chainID at chainID is equal to chainID 
            /\ chains[chainID].clients[chainID] = chainID
            \* the clientID for all other chains at chainID are nullClientID
            \* (the clients for other chains are uninitialized)
            /\ \A otherChainID \in ChainIDs : chains[chainID].clients[otherChainID] = nullClientID
       
    \* initially, all client heights are 0
    /\ clientHeights = [clientID \in ClientIDs |-> nullHeight]
    \* initially, all connection ends are uninitialized
    /\ connectionEnds = [connectionID \in ConnectionIDs |-> nullConnectionEnd]
    \* initially, all channel ends are uninitialized
    /\ channelEnds = [ChannelIDs -> nullChannelEnds]

\* TODO Improve Next.
\* What is the logic of SubmitDatagrams?    
Next ==
    \E chainID \in ChainIDs :
        \E counterpartyID \in ChainIDs :
            IF chainID /= counterpartyID
            THEN LET datagrams == PendingDatagrams(chainID, counterpartyID) IN
                 /\ SubmitDatagrams(chainID, datagrams.local)
                 /\ SubmitDatagrams(counterpartyID, datagrams.counterparty)
            ELSE UNCHANGED vars  


=============================================================================
\* Modification History
\* Last modified Thu Mar 12 13:57:53 CET 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
