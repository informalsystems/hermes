------------------------- MODULE RelayerDefinitions -------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

ChainIDs == {"chainA", "chainB"}
ClientIDs == {"clA", "clB"}
ConnectionIDs == {"connAtoB", "connBtoA"}
ChannelIDs == {"chanAtoB", "chanBtoA"}

nullHeight == 0
nullClientID == "none"
nullConnectionID == "none"
nullChannelID == "none"

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}
ChannelOrder == {"ORDERED", "UNORDERED"}

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

(******************************* ChannelEnds *******************************
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED".
      
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end.
      
      (** ignoring channel ordering for now **) 
 ***************************************************************************)   
ChannelEnds ==
    [
        state : ChannelStates, 
        channelID : ChannelIDs \union {nullChannelID},
        counterpartyChannelID : ChannelIDs \union {nullChannelID}
    ] 

(***************************** ConnectionEnds *****************************
    A set of connection end records. 
    A connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".
    
    - connectionID -- a connection identifier
      Stores the connection identifier of this connection end.
    
    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the counterparty connection end.
    
    - clientID -- a client identifier
      Stores the client identifier associated with this connection end. 
      
    - counterpartyClientID -- a client identifier
      Stores the counterparty client identifier associated with this connection end.
 ***************************************************************************)
ConnectionEnds ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyClientID : ClientIDs \union {nullClientID}, 
        channelEnd : ChannelEnds
    ]  


(********************************** Chains *********************************
    A set of chain records. 
    A chain record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.

    - connectionEnd : a connection end record 
      Stores data about the connection with the counterparty chain
 ***************************************************************************)
Chains ==    
    [
        height : Nat,
        counterpartyClientHeights : SUBSET(Nat),
        connectionEnd : ConnectionEnds
    ]

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(Heights) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : Heights]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights]   
    \union
    [type : {"ConnOpenInit"}, connectionID : ConnectionIDs, clientID : ClientIDs, 
     counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs]
    \union
    [type : {"ConnOpenTry"}, desiredConnectionID : ConnectionIDs, 
     counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs, 
     clientID : ClientIDs, proofHeight : Heights, consensusHeight : Heights]
    \union
    [type : {"ConnOpenAck"}, connectionID : ConnectionIDs, proofHeight : Heights, 
     consensusHeight : Heights ]
    \union
    [type : {"ConnOpenConfirm"}, connectionID : ConnectionIDs, proofHeight : Heights] 
    \union
    [type : {"ChanOpenInit"}, channelID : ChannelIDs, counterpartyChannelID : ChannelIDs] 
    \union 
    [type : {"ChanOpenTry"}, channelID : ChannelIDs, counterpartyChannelID : ChannelIDs, 
     proofHeight : Heights]
    \union 
    [type : {"ChanOpenAck"}, channelID : ChannelIDs, proofHeight : Heights]
    \union
    [type : {"ChanOpenConfirm"}, channelID : ChannelIDs, proofHeight : Heights]

(***************************************************************************
 Initial values of a channel end, connection end, chain
 ***************************************************************************)
\* Initial value of a channel end:
\*      - state is "UNINIT"
\*      - channelID, counterpartyChannelID are uninitialized
InitChannelEnd ==
    [state |-> "UNINIT",
     channelID |-> nullChannelID,
     counterpartyChannelID |-> nullChannelID]  

\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized                             
InitConnectionEnd ==
    [state |-> "UNINIT",
     connectionID |-> nullConnectionID,
     clientID |-> nullClientID,
     counterpartyConnectionID |-> nullConnectionID,
     counterpartyClientID |-> nullClientID,
     channelEnd |-> InitChannelEnd]  

\* Initial value of the chain: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
InitChain ==
    [height |-> 1,
     counterpartyClientHeights |-> {}, 
     connectionEnd |-> InitConnectionEnd]

(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN "clA" ELSE "clB"
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN "clB" ELSE "clA"
    
\* get the latest height of chainID
GetLatestHeight(chain) ==
    chain.height   
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= {}
    THEN Max(chain.counterpartyClientHeights)
    ELSE nullHeight

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chain) ==
    chain.counterpartyClientHeights        

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chain) ==
    chain.counterpartyClientHeights /= {}

\* returns true if the height h is in counterparty client heights on chainID 
IsCounterpartyClientHeightOnChain(chain, h) ==
    h \in chain.counterpartyClientHeights
     
(***************************************************************************
 Connection helper operators
 ***************************************************************************)

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connAtoB"
    ELSE IF chainID = "chainB"
         THEN "connBtoA"
         ELSE nullConnectionID      

\* get the connection ID of the connection end at chainID's counterparty chain
GetCounterpartyConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connBtoA"
    ELSE IF chainID = "chainB"
         THEN "connAtoB"
         ELSE nullConnectionID 
\* get the connection end at chainID
GetConnectionEnd(chain) == 
    chain.connectionEnd

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chain) ==
    chain.connectionEnd.state = "UNINIT"

\* returns true if the connection end on chainID is INIT
IsConnectionInit(chain) ==
    chain.connectionEnd.state = "INIT"

\* returns true if the connection end on chainID is TRYOPEN
IsConnectionTryopen(chain) ==
    chain.connectionEnd.state = "TRYOPEN"
    
\* returns true if the connection end on chainID is OPEN
IsConnectionOpen(chain) ==
    chain.connectionEnd.state = "OPEN"
          
(***************************************************************************
 Channel helper operators
 ***************************************************************************)

\* get the channel ID of the channel end at the connection end of chainID
GetChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanAtoB"
    ELSE IF chainID = "chainB"
         THEN "chanBtoA"
         ELSE nullChannelID
         
\* get the channel ID of the channel end at chainID's counterparty chain
GetCounterpartyChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanBtoA"
    ELSE IF chainID = "chainB"
         THEN "chanAtoB"
         ELSE nullChannelID 
                   
\* get the channel end at the connection end of chainID          
GetChannelEnd(chain) ==
    chain.connectionEnd.channelEnd
    
\* returns true if the channel end on chainID is UNINIT
IsChannelUninit(chain) ==
    chain.connectionEnd.channelEnd.state = "UNINIT"

\* returns true if the channel end on chainID is INIT
IsChannelInit(chain) ==
    chain.connectionEnd.channelEnd.state = "INIT"

\* returns true if the channel end on chainID is TRYOPEN
IsChannelTryopen(chain) ==
    chain.connectionEnd.channelEnd.state = "TRYOPEN"
    
\* returns true if the channel end on chainID is OPEN
IsChannelOpen(chain) ==
    chain.connectionEnd.channelEnd.state = "OPEN"    


=============================================================================
\* Modification History
\* Last modified Wed Jun 24 18:18:13 CEST 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska