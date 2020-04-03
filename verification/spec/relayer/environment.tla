---------------------------- MODULE environment ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight \* maximal height of all the chains in the system

VARIABLES chains, \* a function that assigns to each chainID a chain record 
          pendingDatagrams \* a function that assigns to each chainID a set of pending datagrams
          
vars == <<chains, pendingDatagrams>>

ChainIDs == {"chainA", "chainB"}
ClientIDs == {"clA", "clB"}
ConnectionIDs == {"connAtoB", "connBtoA"}
Heights == 1..MaxHeight

nullClientID == "none"
nullConnectionID == "none"
nullHeight == 0

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

Max(S) == CHOOSE x \in S: \A y \in S: y <= x    

(*** ConnectionEnds ***
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
      
    - TODO: add channel 
**************)    
ConnectionEnds ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyClientID : ClientIDs \union {nullClientID}  
    ]      

(*** Chains ***
    A set of chain records. 
    A chain record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeight : an integer between nullHeight and MaxHeight
      Stores the height of the client for the counterparty chain.

    - connectionEnd : a connection end record 
      Stores data about the connection with the counterparty chain
**************)
Chains ==    
    [
        height : Heights \union {nullHeight},
        counterpartyClientHeight : Heights \union {nullHeight},
        connectionEnd : ConnectionEnds
    ]
    
(*** Datagrams ***
    A set of datagrams.
******************)
Datagrams ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : Heights]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights]   
    \union
    [type : {"ConnOpenInit"}, connectionID : ConnectionIDs, clientID : ClientIDs, counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs]
    \union
    [type : {"ConnOpenTry"}, desiredConnectionID : ConnectionIDs, counterpartyConnectionID : ConnectionIDs, 
     counterpartyClientID : ClientIDs, clientID : ClientIDs, proofHeight : Heights, consensusHeight : Heights]
    \union
    [type : {"ConnOpenAck"}, connectionID : ConnectionIDs, proofHeight : Heights, consensusHeight : Heights ]
    \union
    [type : {"ConnOpenConfirm"}, connectionID : ConnectionIDs, proofHeight : Heights] 

(***************
Chain helper operators
***************)    
\* get the latest height of the chainID
GetLatestHeight(chainID) ==
    chains[chainID].height   
      
\* get the height of the client for chainID's counterparty chain    
GetCounterpartyClientHeight(chainID) ==
    chains[chainID].counterpartyClientHeight

\* get the chain identifier of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN "clA" ELSE "clB"
        
\* get the client ID of the client for the counterparty of chainID           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN "clB" ELSE "clA"     

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chainID) ==
    chains[chainID].counterpartyClientHeight /= nullHeight

\* returns true if the counterparty client height on chainID is greater or equal than height
CounterpartyClientHeightUpdated(chainID, height) ==
    chains[chainID].counterpartyClientHeight >= height

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connAtoB"
    ELSE IF chainID = "chainB"
         THEN "connBtoA"
         ELSE nullConnectionID      

\* get the connection ID of the connection end at the counterparty of chainID
GetCounterpartyConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connBtoA"
    ELSE IF chainID = "chainB"
         THEN "connAtoB"
         ELSE nullConnectionID      

\* get the connection end at chainID
GetConnectionEnd(chainID) == 
    chains[chainID].connectionEnd

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chainID) ==
    chains[chainID].connectionEnd.state = "UNINIT"
    
\* returns true if the connection end on chainID is OPEN
IsConnectionOpen(chainID) ==
    chains[chainID].connectionEnd.state = "OPEN"
          

(***************
Client update operators
***************)

\* Handle "CreateClient" datagrams
HandleCreateClient(chainID, chain, datagrams) == 
    \* get "CreateClient" datagrams with valid clientID
    LET createClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "CreateClient"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET createClientHeights == {h \in Heights : \E dgr \in createClientDgrs : dgr.height = h} IN  
    
    \* new chain record with clients created
    LET clientCreateChain == [
            height |-> chain.height,
            counterpartyClientHeight |-> IF createClientHeights /= {}
                                         THEN Max(createClientHeights)
                                         ELSE chain.counterpartyClientHeight,
            connectionEnd |-> chain.connectionEnd
         ] IN

    IF chain.counterpartyClientHeight = nullHeight
    \* if the counterparty client height is null, create the client   
    THEN clientCreateChain
    \* otherwise, do not update the chain  
    ELSE chain 

\* Handle "ClientUpdate" datagrams
HandleUpdateClient(chainID, chain, datagrams) ==      
    \* get "ClientUpdate" datagrams with valid clientID
    LET updateClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientUpdate"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET updateClientHeights == {h \in Heights : \E dgr \in updateClientDgrs : dgr.height = h} IN    

    \* new chain record with clients updated
    LET clientUpdatedChain == [
            height |-> chain.height,
            counterpartyClientHeight |-> IF updateClientHeights /= {}
                                         THEN Max(updateClientHeights)
                                         ELSE chain.counterpartyClientHeight,
            connectionEnd |-> chain.connectionEnd
         ] IN
    
    IF chain.counterpartyClientHeight < clientUpdatedChain.counterpartyClientHeight
    \* if the current height of the counterparty client is smaller than the new height, update it
    THEN clientUpdatedChain 
    \* otherwise, do not update the chain
    ELSE chain 

\* Update the clients on chain with chainID, 
\* using the client datagrams generated by the relayer      
LightClientUpdate(chainID, chain, datagrams) == 
    \* create clients
    LET clientCreatedChain == HandleCreateClient(chainID, chain, datagrams) IN
    \* update clients
    LET clientUpdatedChain == HandleUpdateClient(chainID, clientCreatedChain, datagrams) IN

    clientUpdatedChain
    
(***************
Connection update operators
***************)

\* Handle "ConnOpenInit" datagrams
HandleConnOpenInit(chainID, chain, datagrams) ==
    \* get "ConnOpenInit" datagrams, with a valid connection ID
    LET connOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenInit"
                            /\ dgr.connectionID = GetConnectionID(chainID)} IN
    
    IF connOpenInitDgrs /= {} 
    \* if there are valid "ConnOpenInit" datagrams, create a new connection end and update the chain
    THEN LET connOpenInitDgr == CHOOSE dgr \in connOpenInitDgrs : TRUE IN
         LET connOpenInitConnectionEnd == [
             state |-> "INIT",
             connectionID |-> connOpenInitDgr.connectionID,
             clientID |-> connOpenInitDgr.clientID,
             counterpartyConnectionID |-> connOpenInitDgr.counterpartyConnectionID,
             counterpartyClientID |-> connOpenInitDgr.counterpartyClientID 
         ] IN 
         LET connOpenInitChain == [
            height |-> chain.height,
            counterpartyClientHeight |-> chain.counterpartyClientHeight,
            connectionEnd |-> connOpenInitConnectionEnd
         ] IN
        
         \* TODO: check here if connection is already in INIT?
         connOpenInitChain
    \* otherwise, do not update the chain     
    ELSE chain

\* TODO height check
\* Handle "ConnOpenTry" datagrams
HandleConnOpenTry(chainID, chain, datagrams) ==
    \* get "ConnOpenTry" datagrams, with a valid connection ID and valid height
    LET connOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenTry"
                            /\ dgr.desiredConnectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight <= chain.counterpartyClientHeight} IN
    
    IF connOpenTryDgrs /= {}
    \* if there are valid "ConnOpenTry" datagrams, update the connection end 
    THEN LET connOpenTryDgr == CHOOSE dgr \in connOpenTryDgrs : TRUE IN
         LET connOpenTryConnectionEnd == [
                state |-> "TRYOPEN",
                connectionID |-> connOpenTryDgr.desiredConnectionID,
                clientID |-> connOpenTryDgr.clientID,
                counterpartyConnectionID |-> connOpenTryDgr.counterpartyConnectionID,
                counterpartyClientID |-> connOpenTryDgr.counterpartyClientID 
            ] IN 
       
         IF \/ chain.connectionEnd.state = "UNINIT"
            \/ /\ chain.connectionEnd.state = "INIT"
               /\ chain.connectionEnd.counterpartyConnectionID = connOpenTryConnectionEnd.counterpartyConnectionID
               /\ chain.connectionEnd.clientID = connOpenTryConnectionEnd.clientID
               /\ chain.connectionEnd.counterpartyClientID = connOpenTryConnectionEnd.counterpartyClientID 
         \* if the connection end on the chain is in "UNINIT" or it is in "INIT",  
         \* but the fields are the same as in the datagram, update the connection end     
         THEN LET connOpenTryChain == [
                     height |-> chain.height,
                     counterpartyClientHeight |-> chain.counterpartyClientHeight,
                     connectionEnd |-> connOpenTryConnectionEnd
                ] IN
                
              \* TODO: check here if connection is already in TRYOPEN?  
              connOpenTryChain
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain

\* TODO look at code for height check
\* Handle "ConnOpenAck" datagrams
HandleConnOpenAck(chainID, chain, datagrams) ==
    \* get "ConnOpenAck" datagrams, with a valid connection ID and valid height
    LET connOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenAck"
                            /\ dgr.connectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height} IN
    
    IF connOpenAckDgrs /= {}
    \* if there are valid "ConnOpenAck" datagrams, update the connection end 
    THEN IF \/ chain.connectionEnd.state = "INIT"
            \/ chain.connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the connection end       
         THEN LET connOpenAckDgr == CHOOSE dgr \in connOpenAckDgrs : TRUE IN
              LET connOpenAckConnectionEnd == [ 
                     state |-> "OPEN",
                     connectionID |-> connOpenAckDgr.connectionID,
                     clientID |-> chain.connectionEnd.clientID,
                     counterpartyConnectionID |-> chain.connectionEnd.counterpartyConnectionID, 
                     counterpartyClientID |-> chain.connectionEnd.counterpartyClientID          
                ] IN
              LET connOpenAckChain == [
                     height |-> chain.height,
                     counterpartyClientHeight |-> chain.counterpartyClientHeight,
                     connectionEnd |-> connOpenAckConnectionEnd
                ] IN
              
              \* TODO: check here if connection is already in OPEN?
              connOpenAckChain                
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain

\* TODO look at code for height check
\* Handle "ConnOpenConfirm" datagrams
HandleConnOpenConfirm(chainID, chain, datagrams) ==
    \* get "ConnOpenConfirm" datagrams, with a valid connection ID and valid height
    LET connOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ConnOpenConfirm"
                                /\ dgr.connectionID = GetConnectionID(chainID)} IN
    
    IF connOpenConfirmDgrs /= {}
    \* if there are valid "connOpenConfirmDgrs" datagrams, update the connection end 
    THEN IF chain.connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "TRYOPEN", update the connection end       
         THEN LET connOpenConfirmDgr == CHOOSE dgr \in connOpenConfirmDgrs : TRUE IN
              LET connOpenConfirmConnectionEnd == [ 
                     state |-> "OPEN",
                     connectionID |-> connOpenConfirmDgr.connectionID,
                     clientID |-> chain.connectionEnd.clientID,
                     counterpartyConnectionID |-> chain.connectionEnd.counterpartyConnectionID, 
                     counterpartyClientID |-> chain.connectionEnd.counterpartyClientID          
                ] IN
              LET connOpenConfirmChain == [
                     height |-> chain.height,
                     counterpartyClientHeight |-> chain.counterpartyClientHeight,
                     connectionEnd |-> connOpenConfirmConnectionEnd
                ] IN
              
              \* TODO: check here if connection is already in OPEN?
              connOpenConfirmChain                
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain

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

(***************
Channel update operators
***************)    

\* Handle "ChanOpenInit" datagrams
HandleChanOpenInit(chainID, chain, datagrams) ==
    \* TODO
    chain

\* Handle "ChanOpenTry" datagrams
HandleChanOpenTry(chainID, chain, datagrams) ==
    \* TODO
    chain

\* Handle "ChanOpenAck" datagrams
HandleChanOpenAck(chainID, chain, datagrams) ==
    \* TODO
    chain

\* Handle "ChanOpenConfirm" datagrams
HandleChanOpenConfirm(chainID, chain, datagrams) ==
    \* TODO
    chain

\* Update the channels on chain with chainID, 
\* using the channel datagrams generated by the relayer
ChannelUpdate(chainID, chain, datagrams) ==
    \* update chain with "ChanOpenInit" datagrams
    LET chanInit == HandleChanOpenInit(chainID, chain, datagrams) IN
    \* update chain with "ChanOpenTry" datagrams
    LET chanTry == HandleChanOpenTry(chainID, chanInit, datagrams) IN
    \* update chain with "ChanOpenAck" datagrams
    LET chanAck == HandleChanOpenAck(chainID, chanTry, datagrams) IN
    \* update chain with "ChanOpenConfirm" datagrams
    LET chanConfirm == HandleChanOpenConfirm(chainID, chanAck, datagrams) IN
    
    chanConfirm
    


(***************
Chain update operators
***************) 
 
\* Update chainID with the received datagrams
\* Currently, only supporting ICS 002: Client updates
UpdateChain(chainID, datagrams) == 
    LET chain == chains[chainID] IN
    \* ICS 002: Client updates
    LET lightClientsUpdated == LightClientUpdate(chainID, chain, datagrams) IN 
    \* ICS 003: Connection updates
    LET connectionsUpdated == ConnectionUpdate(chainID, lightClientsUpdated, datagrams) IN
    \* ICS 004: Channel updates
    LET channelsUpdated == ChannelUpdate(chainID, connectionsUpdated, datagrams) IN
    
    channelsUpdated
    
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


\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized                             
InitConnectionEnd ==
    [state |-> "UNINIT",
     connectionID |-> nullConnectionID,
     clientID |-> nullClientID,
     counterpartyConnectionID |-> nullConnectionID,
     counterpartyClientID |-> nullClientID]  

\* Initial value of the chain: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
InitChain ==
    [height |-> 1,
     counterpartyClientHeight |-> nullHeight, 
     connectionEnd |-> InitConnectionEnd]

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
\*    One of the chains either
\*        - advances its height
\*        - receives datagrams and updates its state
Next == 
    \/ AdvanceChain
    \/ ReceiveDatagrams
    \/ UNCHANGED vars

\* Fairness constraints 
Fairness ==
    /\ WF_vars(AdvanceChain)
    /\ WF_vars(ReceiveDatagrams) 
 
(************
Invariants
************)

\* Type invariant           
TypeOK ==    
    /\ chains \in [ChainIDs -> Chains]
    /\ pendingDatagrams \in [ChainIDs -> SUBSET Datagrams]     

=============================================================================
\* Modification History
\* Last modified Fri Apr 03 16:36:29 CEST 2020 by ilinastoilkovska
\* Created Fri Mar 13 19:48:22 CET 2020 by ilinastoilkovska
