------------------------------ MODULE Relayer ------------------------------

(***************************************************************************
 This module contains the specification of a relayer, which is an off-chain 
 process running a relayer algorithm 
 ***************************************************************************)

EXTENDS Integers, FiniteSets, RelayerDefinitions

CONSTANTS GenerateClientDatagrams, \* toggle generation of client datagrams
          GenerateConnectionDatagrams, \* toggle generation of connection datagrams
          GenerateChannelDatagrams \* toggle generation of channel datagrams

ASSUME /\ GenerateClientDatagrams \in BOOLEAN 
       /\ GenerateConnectionDatagrams \in BOOLEAN 
       /\ GenerateChannelDatagrams \in BOOLEAN 

CONSTANTS MaxHeight, \* set of possible heights of the chains in the system
          MaxPacketSeq  \* maximal packet sequence number

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          outgoingDatagrams, \* a function that assigns a set of pending datagrams 
                             \* outgoing from the relayer to each chainID 
          relayerHeights, \* a function that assigns a height to each chainID
          closeChannelA, \* flag that triggers closing of the channel end at ChainA
          closeChannelB, \* flag that triggers closing of the channel end at ChainB
          packetLog         
          
vars == <<chainAstore, chainBstore, outgoingDatagrams, relayerHeights, packetLog>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system                     

GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
    
GetCloseChannelFlag(chainID) ==
    IF chainID = "chainA"
    THEN closeChannelA
    ELSE closeChannelB
 
(***************************************************************************
 Client datagrams
 ***************************************************************************)
\* Compute client datagrams designated for dstChainID. 
\* These are used to update the client for srcChainID on dstChainID.
\* Some client updates might trigger an update of the height that 
\* the relayer stores for srcChainID
LightClientUpdates(srcChainID, dstChainID, relayer) ==
    LET srcChain == GetChainByID(srcChainID) IN
    LET dstChain == GetChainByID(dstChainID) IN
    LET srcChainHeight == GetLatestHeight(srcChain) IN    
    LET srcClientHeight == GetMaxCounterpartyClientHeight(dstChain) IN
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
        IF srcClientHeight = AsInt(nullHeight)
        THEN \* the src client does not exist on dstChainID 
            AsSetDatagrams({[type |-> "CreateClient", 
              height |-> srcChainHeight,
              clientID |-> srcClientID]}) 
        ELSE \* the src client exists on dstChainID
            IF srcClientHeight < srcChainHeight
            THEN \* the height of the src client on dstChainID is smaller than the height of the src chain
                AsSetDatagrams({[type |-> "ClientUpdate",
                  height |-> srcChainHeight,
                  clientID |-> srcClientID]}) 
            ELSE AsSetDatagrams({}) IN                   
                    
    [datagrams|-> AsSetDatagrams(dstDatagrams), relayerUpdate |-> updatedRelayer]    
   
(***************************************************************************
 Connection datagrams
 ***************************************************************************)    
\* Compute connection datagrams designated for dstChainID. 
\* These are used to update the connection end on dstChainID.
ConnectionDatagrams(srcChainID, dstChainID) ==
    LET srcChain == GetChainByID(srcChainID) IN
    LET dstChain == GetChainByID(dstChainID) IN
    
    LET srcConnectionEnd == GetConnectionEnd(srcChain) IN
    LET dstConnectionEnd == GetConnectionEnd(dstChain) IN

    LET srcConnectionID == GetConnectionID(srcChainID) IN
    LET dstConnectionID == GetConnectionID(dstChainID) IN

    LET srcHeight == GetLatestHeight(srcChain) IN
    LET srcClientHeight == GetMaxCounterpartyClientHeight(srcChain) IN
    
    IF dstConnectionEnd.state = "UNINIT" /\ srcConnectionEnd.state = "UNINIT" THEN 
         AsSetDatagrams({[type |-> "ConnOpenInit", 
           connectionID |-> dstConnectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           clientID |-> GetCounterpartyClientID(dstChainID), \* "clA"
           counterpartyConnectionID |-> srcConnectionID, \* "connAtoB"
           counterpartyClientID |-> GetCounterpartyClientID(srcChainID)]}) \* "clB" 
    
    ELSE IF srcConnectionEnd.state = "INIT" /\ \/ dstConnectionEnd.state = "UNINIT"
                                               \/ dstConnectionEnd.state = "INIT" THEN 
         AsSetDatagrams({[type |-> "ConnOpenTry",
           connectionID |-> dstConnectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           clientID |-> srcConnectionEnd.counterpartyClientID, \* "clA"
           counterpartyConnectionID |-> srcConnectionID, \* "connAtoB"
           counterpartyClientID |-> srcConnectionEnd.clientID, \* "clB" 
           proofHeight |-> srcHeight,
           consensusHeight |-> srcClientHeight]})
         
    ELSE IF srcConnectionEnd.state = "TRYOPEN" /\ \/ dstConnectionEnd.state = "INIT"
                                                  \/ dstConnectionEnd.state = "TRYOPEN" THEN
         AsSetDatagrams({[type |-> "ConnOpenAck",
           connectionID |-> dstConnectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight,
           consensusHeight |-> srcClientHeight]})
         
    ELSE IF srcConnectionEnd.state = "OPEN" /\ dstConnectionEnd.state = "TRYOPEN" THEN
         AsSetDatagrams({[type |-> "ConnOpenConfirm",
           connectionID |-> dstConnectionEnd.connectionID, \* "connBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight]}) 
    ELSE AsSetDatagrams({})

(***************************************************************************
 Channel handshake datagrams
 ***************************************************************************)
\* Compute channel datagrams designated for dstChainID. 
\* These are used to update the channel end on dstChainID.
ChannelDatagrams(srcChainID, dstChainID) ==
    LET srcChain == GetChainByID(srcChainID) IN
    LET dstChain == GetChainByID(dstChainID) IN

    LET srcChannelEnd == GetChannelEnd(srcChain) IN
    LET dstChannelEnd == GetChannelEnd(dstChain) IN
    
    LET srcChannelID == GetChannelID(srcChainID) IN
    LET dstChannelID == GetChannelID(dstChainID) IN

    LET srcHeight == GetLatestHeight(srcChain) IN
    
    LET dstCloseChannel == GetCloseChannelFlag(dstChainID) IN 
    
    IF dstChannelEnd.state = "UNINIT" /\ srcChannelEnd.state = "UNINIT" THEN 
         AsSetDatagrams({[type |-> "ChanOpenInit", 
           channelID |-> dstChannelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           counterpartyChannelID |-> srcChannelID]}) \* "chanAtoB" 
    
    ELSE IF srcChannelEnd.state = "INIT" /\ \/ dstChannelEnd.state = "UNINIT"
                                            \/ dstChannelEnd.state = "INIT" THEN 
         AsSetDatagrams({[type |-> "ChanOpenTry",
           channelID |-> dstChannelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           counterpartyChannelID |-> srcChannelID, \* "chanAtoB"
           proofHeight |-> srcHeight]}) 
         
    ELSE IF srcChannelEnd.state = "TRYOPEN" /\ \/ dstChannelEnd.state = "INIT"
                                               \/ dstChannelEnd.state = "TRYOPEN" THEN
         AsSetDatagrams({[type |-> "ChanOpenAck",
           channelID |-> dstChannelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight]}) 
         
    ELSE IF srcChannelEnd.state = "OPEN" /\ dstChannelEnd.state = "TRYOPEN" THEN
         AsSetDatagrams({[type |-> "ChanOpenConfirm",
           channelID |-> dstChannelEnd.channelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
           proofHeight |-> srcHeight]}) 
    
    \* channel closing datagrams creation only for open channels
    ELSE IF dstChannelEnd.state = "OPEN" /\ GetCloseChannelFlag(dstChannelID) THEN
         AsSetDatagrams({[type |-> "ChanCloseInit", 
           channelID |-> dstChannelEnd.channelID]}) \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           
    ELSE IF srcChannelEnd.state = "CLOSED" /\ dstChannelEnd.state /= "CLOSED" /\ dstChannelEnd.state /= "UNINIT" THEN 
         AsSetDatagrams({[type |-> "ChanCloseConfirm", 
           channelID |-> dstChannelEnd.channelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           proofHeight |-> srcHeight]})
    
    (** channel closing datagrams creation for channels which are still in handshake: 
        the propery ChanOpenInitDelivery is violated
              
    ELSE IF dstChannelEnd.state /= "CLOSED" /\ dstChannelEnd.state /= "UNINIT" /\ GetCloseChannelFlag(dstChannelID) THEN
         {[type |-> "ChanCloseInit", 
           channelID |-> dstChannelEnd.channelID]} \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           
    ELSE IF srcChannelEnd.state = "CLOSED" /\ dstChannelEnd.state /= "CLOSED" /\ dstChannelEnd.state /= "UNINIT" THEN 
         {[type |-> "ChanCloseConfirm", 
           channelID |-> dstChannelEnd.channelID, \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")  
           proofHeight |-> srcHeight]}
    **)
           
    ELSE AsSetDatagrams({})


(***************************************************************************
 Compute datagrams (from srcChainID to dstChainID)
 ***************************************************************************)
\* Currently supporting:
\*  -  ICS 002: Client updates
\*  -  ICS 003: Connection handshake
\*  -  ICS 004: Channel handshake
\*  -  ICS 004: Packet transmission
ComputeDatagrams(srcChainID, dstChainID) ==
    \* ICS 002 : Clients
    \* - Determine if light clients needs to be updated 
    LET clientDatagrams == 
        IF GenerateClientDatagrams 
        THEN LightClientUpdates(srcChainID, dstChainID, relayerHeights) 
        ELSE [datagrams |-> AsSetDatagrams({}), relayerUpdate |-> relayerHeights] IN
    
    \* ICS3 : Connections
    \* - Determine if any connection handshakes are in progress
    LET connectionDatagrams == 
        IF GenerateConnectionDatagrams
        THEN AsSetDatagrams(ConnectionDatagrams(srcChainID, dstChainID)) 
        ELSE AsSetDatagrams({}) IN
    
    \* ICS4 : Channels & Packets
    \* - Determine if any channel handshakes are in progress
    LET channelDatagrams == 
        IF GenerateChannelDatagrams 
        THEN AsSetDatagrams(ChannelDatagrams(srcChainID, dstChainID)) 
        ELSE AsSetDatagrams({}) IN
    
    
    [datagrams |-> AsSetDatagrams(clientDatagrams.datagrams \union 
                   connectionDatagrams \union 
                   channelDatagrams), 
     relayerUpdate |-> clientDatagrams.relayerUpdate]

(***************************************************************************
 Relayer actions
 ***************************************************************************)   
\* Update the height of the relayer client for some chainID
UpdateRelayerClients(chainID) ==
    LET chainLatestHeight == GetLatestHeight(GetChainByID(chainID)) IN
    /\ relayerHeights[chainID] < chainLatestHeight
    /\ relayerHeights' = [relayerHeights EXCEPT 
                            ![chainID] = GetLatestHeight(GetChainByID(chainID))
                         ]
    /\ UNCHANGED <<chainAstore, chainBstore, outgoingDatagrams, packetLog>>  

\* for two chains, srcChainID and dstChainID, where srcChainID /= dstChainID, 
\* create the pending datagrams and update the corresponding sets of pending datagrams
Relay(srcChainID, dstChainID) ==
    LET datagramsAndRelayerUpdate == ComputeDatagrams(srcChainID, dstChainID) IN
    /\ srcChainID /= dstChainID
    /\ outgoingDatagrams' = 
            [outgoingDatagrams EXCEPT 
                ![dstChainID] = AsSetDatagrams(outgoingDatagrams[dstChainID] 
                                \union 
                                datagramsAndRelayerUpdate.datagrams)
            ]
    /\ relayerHeights' = datagramsAndRelayerUpdate.relayerUpdate       
    /\ UNCHANGED <<chainAstore, chainBstore, packetLog>>

UpdateRelayer ==
    \E chainID \in ChainIDs : UpdateRelayerClients(chainID)
    
CreateDatagrams ==
    \E srcChainID \in ChainIDs : \E dstChainID \in ChainIDs : Relay(srcChainID, dstChainID)    

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\*    Initially:
\*        - the relayer heights are uninitialized (i.e., their height is nullHeight)
Init == 
    /\ relayerHeights = [chainID \in ChainIDs |-> AsInt(nullHeight)]
    /\ outgoingDatagrams = [chainID \in ChainIDs |-> AsSetDatagrams({})]
    
\* Next state action
\*    The relayer either:
\*        - updates its clients, or
\*        - relays datagrams between two chains, or
\*        - does nothing
Next ==
    \/ UpdateRelayer
    \/ CreateDatagrams
    \/ UNCHANGED vars    
       
\* Fairness constraints
Fairness ==
    /\ \A chainID \in ChainIDs : 
            WF_vars(UpdateRelayerClients(chainID))
    /\ \A srcChainID \in ChainIDs : \A dstChainID \in ChainIDs : 
            WF_vars(Relay(srcChainID, dstChainID))
               
(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant
TypeOK ==
    /\ relayerHeights \in [ChainIDs -> Heights \union {nullHeight}]
    /\ outgoingDatagrams \in [ChainIDs -> SUBSET Datagrams(MaxHeight, MaxPacketSeq)]

=============================================================================
\* Modification History
\* Last modified Tue Aug 11 12:50:40 CEST 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
