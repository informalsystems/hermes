---------------------------- MODULE Environment ----------------------------

(***************************************************************************
 This module captures the chain logic. It extends the modules ClientHandlers, 
 ConnectionHandlers, and ChannelHandlers, which contain definitions of 
 operators that handle the client, connection, and channel datagrams, 
 respectively.  
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, ClientHandlers, ConnectionHandlers, ChannelHandlers

VARIABLES chains, \* a function that assigns a chain record to each chainID  
          incomingDatagrams \* a function that assigns a set of incoming datagrams 
                            \* incoming from the relayer to each chainID 
          
vars == <<chains, incomingDatagrams>>

ChainIDs == {"chainA", "chainB"}

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
        height : Heights \union {nullHeight},
        counterpartyClientHeights : SUBSET(Heights),
        connectionEnd : ConnectionEnds
    ]
    
(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams ==
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
 Chain helper operators
 ***************************************************************************)
\* get the latest height of chainID
GetLatestHeight(chainID) ==
    chains[chainID].height   
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chainID) ==
    IF chains[chainID].counterpartyClientHeights /= {}
    THEN Max(chains[chainID].counterpartyClientHeights)
    ELSE nullHeight

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chainID) ==
    chains[chainID].counterpartyClientHeights        

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chainID) ==
    chains[chainID].counterpartyClientHeights /= {}

\* returns true if the counterparty client height on chainID is greater or equal than h
CounterpartyClientHeightUpdated(chainID, h) ==
    h \in chains[chainID].counterpartyClientHeights

\* get the connection end at chainID
GetConnectionEnd(chainID) == 
    chains[chainID].connectionEnd

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chainID) ==
    chains[chainID].connectionEnd.state = "UNINIT"

\* returns true if the connection end on chainID is INIT
IsConnectionInit(chainID) ==
    chains[chainID].connectionEnd.state = "INIT"

\* returns true if the connection end on chainID is TRYOPEN
IsConnectionTryopen(chainID) ==
    chains[chainID].connectionEnd.state = "TRYOPEN"
    
\* returns true if the connection end on chainID is OPEN
IsConnectionOpen(chainID) ==
    chains[chainID].connectionEnd.state = "OPEN"
          
\* get the channel end at the connection end of chainID          
GetChannelEnd(chainID) ==
    chains[chainID].connectionEnd.channelEnd
    
\* returns true if the channel end on chainID is UNINIT
IsChannelUninit(chainID) ==
    chains[chainID].connectionEnd.channelEnd.state = "UNINIT"

\* returns true if the channel end on chainID is INIT
IsChannelInit(chainID) ==
    chains[chainID].connectionEnd.channelEnd.state = "INIT"

\* returns true if the channel end on chainID is TRYOPEN
IsChannelTryopen(chainID) ==
    chains[chainID].connectionEnd.channelEnd.state = "TRYOPEN"
    
\* returns true if the channel end on chainID is OPEN
IsChannelOpen(chainID) ==
    chains[chainID].connectionEnd.channelEnd.state = "OPEN"    

(***************************************************************************
 Client update operators
 ***************************************************************************)
\* Update the clients on chain with chainID, 
\* using the client datagrams generated by the relayer      
LightClientUpdate(chainID, chain, datagrams) == 
    \* create clients
    LET clientCreatedChain == HandleCreateClient(chainID, chain, datagrams) IN
    \* update clients
    LET clientUpdatedChain == HandleUpdateClient(chainID, clientCreatedChain, datagrams) IN

    clientUpdatedChain
    
(***************************************************************************
 Connection update operators
 ***************************************************************************)
\* Update the connections on chain with chainID, 
\* using the connection datagrams generated by the relayer
ConnectionUpdate(chainID, chain, datagrams) ==
    \* update chain with "ConnOpenInit" datagrams
    LET connOpenInitChain == HandleConnOpenInit(chainID, chain, datagrams) IN
    \* update chain with "ConnOpenTry" datagrams
    LET connOpenTryChain == HandleConnOpenTry(chainID, connOpenInitChain, datagrams) IN
    \* update chain with "ConnOpenAck" datagrams
    LET connOpenAckChain == HandleConnOpenAck(chainID, connOpenTryChain, datagrams) IN
    \* update chain with "ConnOpenConfirm" datagrams
    LET connOpenConfirmChain == HandleConnOpenConfirm(chainID, connOpenAckChain, datagrams) IN
    
    connOpenConfirmChain

(***************************************************************************
 Channel update operators
 ***************************************************************************)
\* Update the channels on chain with chainID, 
\* using the channel datagrams generated by the relayer
ChannelUpdate(chainID, chain, datagrams) ==
    \* update chain with "ChanOpenInit" datagrams
    LET chanOpenInitChain == HandleChanOpenInit(chainID, chain, datagrams) IN
    \* update chain with "ChanOpenTry" datagrams
    LET chanOpenTryChain == HandleChanOpenTry(chainID, chanOpenInitChain, datagrams) IN
    \* update chain with "ChanOpenAck" datagrams
    LET chanOpenAckChain == HandleChanOpenAck(chainID, chanOpenTryChain, datagrams) IN
    \* update chain with "ChanOpenConfirm" datagrams
    LET chanOpenConfirmChain == HandleChanOpenConfirm(chainID, chanOpenAckChain, datagrams) IN
    
    chanOpenConfirmChain
    
(***************************************************************************
 Chain update operators
 ***************************************************************************)
\* Update chainID with the received datagrams
\* Supports ICS2 (Clients), ICS3 (Connections), and ICS4 (Channels).
UpdateChain(chainID, datagrams) == 
    LET chain == chains[chainID] IN
    \* ICS 002: Client updates
    LET lightClientsUpdated == LightClientUpdate(chainID, chain, datagrams) IN 
    \* ICS 003: Connection updates
    LET connectionsUpdated == ConnectionUpdate(chainID, lightClientsUpdated, datagrams) IN
    \* ICS 004: Channel updates
    LET channelsUpdated == ChannelUpdate(chainID, connectionsUpdated, datagrams) IN
    
    \* update height
    LET updatedChain == 
        IF /\ chain /= channelsUpdated
           /\ chain.height < MaxHeight 
        THEN [channelsUpdated EXCEPT !.height = chain.height + 1]
        ELSE channelsUpdated
    IN
    
    updatedChain
    
(***************************************************************************
 Chain actions
 ***************************************************************************)       
\* Advance the height of the chain until MaxHeight is reached
AdvanceChain(chainID) ==
    /\ chains[chainID].height < MaxHeight
    /\ chains' = [chains EXCEPT 
                    ![chainID].height = chains[chainID].height + 1                                            
                 ]
    /\ UNCHANGED incomingDatagrams

\* Receive the datagrams and update the chain state        
ReceiveDatagrams(chainID) ==
    /\ incomingDatagrams[chainID] /= {} 
    /\ chains' = [chains EXCEPT 
                    ![chainID] = UpdateChain(chainID, incomingDatagrams[chainID])
                 ]
    /\ incomingDatagrams' = [incomingDatagrams EXCEPT
                                ![chainID] = {}
                           ]

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
 Specification
 ***************************************************************************)
\* Initial state predicate
\*    Initially
\*        - each chain is initialized to InitChain
\*        - pendingDatagrams for each chain is empty
Init ==    
    /\ chains = [chainID \in ChainIDs |-> InitChain]
    /\ incomingDatagrams = [chainID \in ChainIDs |-> {}]

\* Next state action
\*    One of the chains either
\*        - advances its height
\*        - receives datagrams and updates its state
Next == 
    \E chainID \in ChainIDs :
        \/ AdvanceChain(chainID)
        \/ ReceiveDatagrams(chainID)
        \/ UNCHANGED vars

\* Fairness constraints 
Fairness ==
    \* ensure all chains take steps
    /\ \A chainID \in ChainIDs : WF_vars(AdvanceChain(chainID))
    /\ \A chainID \in ChainIDs : WF_vars(ReceiveDatagrams(chainID))
 
(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant           
TypeOK ==    
    /\ chains \in [ChainIDs -> Chains]
    /\ incomingDatagrams \in [ChainIDs -> SUBSET Datagrams]     

=============================================================================
\* Modification History
\* Last modified Fri May 22 17:09:26 CEST 2020 by ilinastoilkovska
\* Created Fri Mar 13 19:48:22 CET 2020 by ilinastoilkovska
