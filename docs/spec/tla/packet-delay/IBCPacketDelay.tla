--------------------------- MODULE IBCPacketDelay ---------------------------

EXTENDS Integers, FiniteSets, Sequences, IBCPacketDelayDefinitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          ChannelOrdering, \* indicate whether the channels are ordered or unordered
          MaxPacketSeq, \* maximal packet sequence number
          MaxDelay \* maximal packet delay

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          packetDatagramsChainA, \* sequence of packet datagrams incoming to ChainA
          packetDatagramsChainB, \* sequence of packet datagrams incoming to ChainB
          outgoingPacketDatagrams, \* packet datagrams created by the relayer but not submitted
          packetLog, \* packet log
          appPacketSeqChainA, \* packet sequence number from the application on ChainA
          appPacketSeqChainB, \* packet sequence number from the application on ChainB
          packetDatagramTimestamp \* history variable that tracks when packet datagrams were processed
           
chainAvars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA>>
chainBvars == <<chainBstore, packetDatagramsChainB, appPacketSeqChainB>>
vars == <<chainAstore, chainBstore,
          packetDatagramsChainA, packetDatagramsChainB,
          outgoingPacketDatagrams, packetLog, 
          appPacketSeqChainA, appPacketSeqChainB,
          packetDatagramTimestamp>>
(***************************************************************************
 Instances of Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               chainStore <- chainAstore,
               incomingPacketDatagrams <- packetDatagramsChainA,    
               appPacketSeq <- appPacketSeqChainA    

\* ChainB -- Instance of Chain.tla
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               chainStore <- chainBstore,
               incomingPacketDatagrams <- packetDatagramsChainB,
               appPacketSeq <- appPacketSeqChainB   
               

 (***************************************************************************
 Environment operators
 ***************************************************************************)

\* get chain store by ID
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
               
\* update the client height of the client for the counterparty chain of chainID
UpdateClientHeights(chainID) ==
    /\ \/ /\ chainID = "chainA"
          /\ chainBstore.height \notin DOMAIN chainAstore.counterpartyClientHeights
          /\ chainAstore' = [chainAstore EXCEPT 
                              !.counterpartyClientHeights = 
                                [h \in DOMAIN chainAstore.counterpartyClientHeights \union {chainBstore.height} |->
                                    IF h = chainBstore.height
                                    THEN chainAstore.timestamp
                                    ELSE chainAstore.counterpartyClientHeights[h]],
                              !.timestamp = chainAstore.timestamp + 1
                            ]
          /\ UNCHANGED chainBstore
       \/ /\ chainID = "chainB"
          /\ chainAstore.height \notin DOMAIN chainBstore.counterpartyClientHeights
          /\ chainBstore' = [chainBstore EXCEPT 
                              !.counterpartyClientHeights = 
                                [h \in DOMAIN chainBstore.counterpartyClientHeights \union {chainAstore.height} |->
                                    IF h = chainAstore.height
                                    THEN chainBstore.timestamp
                                    ELSE chainBstore.counterpartyClientHeights[h]],
                              !.timestamp = chainBstore.timestamp + 1
                            ]
          /\ UNCHANGED chainAstore
       \/ UNCHANGED <<chainAstore, chainBstore>>
    /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB, packetDatagramTimestamp>>
    /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB, outgoingPacketDatagrams, packetLog>>


\* Compute a packet datagram designated for dstChainID, based on the packetLogEntry
PacketDatagram(srcChainID, dstChainID, packetLogEntry) ==
    
    LET srcChannelID == GetChannelID(srcChainID) IN \* "chanAtoB" (if srcChainID = "chainA")
    LET dstChannelID == GetChannelID(dstChainID) IN \* "chanBtoA" (if dstChainID = "chainB")
    
    LET srcPortID == GetPortID(srcChainID) IN \* "portA" (if srcChainID = "chainA")
    LET dstPortID == GetPortID(dstChainID) IN \* "portB" (if dstChainID = "chainB")
    
    LET srcHeight == GetLatestHeight(GetChainByID(srcChainID)) IN
    
    \* the source chain of the packet that is received by dstChainID is srcChainID
    LET recvPacket(logEntry) == [sequence |-> logEntry.sequence, 
                                 timeoutHeight |-> logEntry.timeoutHeight,
                                 srcChannelID |-> srcChannelID,
                                 srcPortID |-> srcPortID,
                                 dstChannelID |-> dstChannelID,
                                 dstPortID |-> dstPortID] IN
                                 
    \* the source chain of the packet that is acknowledged by srcChainID is dstChainID
    LET ackPacket(logEntry) == [sequence |-> logEntry.sequence, 
                                 timeoutHeight |-> logEntry.timeoutHeight,
                                 srcChannelID |-> dstChannelID,
                                 srcPortID |-> dstPortID,
                                 dstChannelID |-> srcChannelID,
                                 dstPortID |-> srcPortID] IN                                 
    
    IF packetLogEntry.type = "PacketSent"
    THEN [type |-> "PacketRecv",
          packet |-> recvPacket(packetLogEntry),  
          proofHeight |-> srcHeight]
    ELSE IF packetLogEntry.type = "WriteAck"
         THEN [type |-> "PacketAck",
                  packet |-> ackPacket(packetLogEntry),
                  acknowledgement |-> packetLogEntry.acknowledgement,  
                  proofHeight |-> srcHeight]
         ELSE NullDatagram 
                        
\* submit a packet datagram if a delay has passed 
\* or install the appropriate height if it is missing
SubmitDatagramOrInstallClientHeight(chainID) == 
    LET packetDatagram == Head(outgoingPacketDatagrams[chainID]) IN
    LET chain == GetChainByID(chainID) IN
    
    LET clientHeightTimestamp == 
        IF packetDatagram.proofHeight \in DOMAIN chain.counterpartyClientHeights
        THEN chain.counterpartyClientHeights[packetDatagram.proofHeight]
        ELSE 0 IN   
   
   \* packetDatagram.proof height is installed on chain  
   IF clientHeightTimestamp /= 0  
        \* the delay has passed
   THEN IF clientHeightTimestamp + MaxDelay < chain.timestamp
        \* submit the datagram to the corresponding chain
        THEN LET datagramsChainA == IF chainID = "chainA"
                                    THEN Append(packetDatagramsChainA, packetDatagram)
                                    ELSE packetDatagramsChainA IN
             LET datagramsChainB == IF chainID = "chainB"
                                    THEN Append(packetDatagramsChainB, packetDatagram)
                                    ELSE packetDatagramsChainB IN
             LET outgoingDatagrams == [outgoingPacketDatagrams EXCEPT 
                                        ![chainID] = Tail(outgoingPacketDatagrams[chainID])] IN
                                        
             [datagramsChainA |-> datagramsChainA,
              datagramsChainB |-> datagramsChainB,
              outgoingDatagrams |-> outgoingDatagrams,
              chainA |-> chainAstore,
              chainB |-> chainBstore] 
        \* otherwise do not submit and do not install any new heights
        ELSE [datagramsChainA |-> packetDatagramsChainA,
              datagramsChainB |-> packetDatagramsChainB,
              outgoingDatagrams |-> outgoingPacketDatagrams,
              chainA |-> chainAstore,
              chainB |-> chainBstore]
   \* packetDatagram.proof height is not installed on chain, 
   \* install it
   ELSE LET chainA == IF chainID = "chainA"
                      THEN [chainAstore EXCEPT 
                              !.counterpartyClientHeights = 
                                [h \in DOMAIN chainAstore.counterpartyClientHeights \union {packetDatagram.proofHeight} |->
                                    IF h = packetDatagram.proofHeight
                                    THEN chainAstore.timestamp
                                    ELSE chainAstore.counterpartyClientHeights[h]],
                              !.timestamp = chainAstore.timestamp + 1
                            ]
                      ELSE chainAstore IN
        LET chainB == IF chainID = "chainB"
                      THEN [chainBstore EXCEPT 
                              !.counterpartyClientHeights = 
                                [h \in DOMAIN chainBstore.counterpartyClientHeights \union {packetDatagram.proofHeight} |->
                                    IF h = packetDatagram.proofHeight
                                    THEN chainBstore.timestamp
                                    ELSE chainBstore.counterpartyClientHeights[h]],
                              !.timestamp = chainBstore.timestamp + 1
                            ]
                      ELSE chainBstore IN
                      
        [datagramsChainA |-> packetDatagramsChainA,
         datagramsChainB |-> packetDatagramsChainB,
         outgoingDatagrams |-> outgoingPacketDatagrams,
         chainA |-> chainA,
         chainB |-> chainB] 
         
(***************************************************************************
 Environment actions
 ***************************************************************************)
 \* update the client height of some chain
 UpdateClients ==
    \E chainID \in ChainIDs : UpdateClientHeights(chainID) 
 
\* create datagrams depending on packet log
CreateDatagrams ==
    /\ packetLog /= <<>>
    /\ LET packetLogEntry == Head(packetLog) IN
       LET srcChainID == packetLogEntry.srcChainID IN
       LET dstChainID == GetCounterpartyChainID(srcChainID) IN
       LET packetDatagram == PacketDatagram(srcChainID, dstChainID, packetLogEntry) IN
        /\ \/ /\ packetDatagram = NullDatagram
              /\ UNCHANGED outgoingPacketDatagrams
           \/ /\ packetDatagram /= NullDatagram 
              /\ outgoingPacketDatagrams' = 
                        [chainID \in ChainIDs |-> 
                            IF chainID = dstChainID
                            THEN Append(outgoingPacketDatagrams[chainID], packetDatagram)  
                            ELSE outgoingPacketDatagrams[chainID]
                        ]        
        /\ packetLog' = Tail(packetLog)    
        /\ UNCHANGED <<chainAstore, chainBstore>>
        /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB>>
        /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB, packetDatagramTimestamp>>

\* submit datagrams if delay has passed
SubmitDatagramsWithDelay ==
    \E chainID \in ChainIDs : 
        /\ outgoingPacketDatagrams[chainID] /= <<>>
        /\ LET submitted == SubmitDatagramOrInstallClientHeight(chainID) IN
            /\ packetDatagramsChainA' = submitted.datagramsChainA
            /\ packetDatagramsChainB' = submitted.datagramsChainB
            /\ outgoingPacketDatagrams' = submitted.outgoingDatagrams
            /\ chainAstore' = submitted.chainA
            /\ chainBstore' = submitted.chainB
            /\ UNCHANGED <<packetLog, appPacketSeqChainA, appPacketSeqChainB, packetDatagramTimestamp>>
        
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchange
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
       /\ UNCHANGED outgoingPacketDatagrams
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars
       /\ UNCHANGED outgoingPacketDatagrams

\* EnvironmentAction: either 
\*  - create packet datagrams if packet log is not empty, or
\*  - update counterparty clients, or
\*  - submit datagrams after their delay has passed
EnvironmentAction ==
    \/ CreateDatagrams    
    \/ UpdateClients
    \/ SubmitDatagramsWithDelay
    
(***************************************************************************
 Specification
 ***************************************************************************)    
               
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    /\ outgoingPacketDatagrams = [chainID \in ChainIDs |-> <<>>] 
    /\ packetLog = <<>>    
    /\ packetDatagramTimestamp = [x \in {} |-> 0]
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
    
Spec == Init /\ [][Next]_vars       

(***************************************************************************
 Invariants
 ***************************************************************************)

\* each packet datagam is processed at time t (stored in packetDatagramTimestamp), 
\* such that t > ht + delay, where 
\* ht is the time when the client height is installed  
PacketDatagramsDelay ==
    \A chainID \in ChainIDs : 
        \A h \in DOMAIN GetChainByID(chainID).counterpartyClientHeights :
            <<chainID, h>> \in DOMAIN packetDatagramTimestamp
            =>
            packetDatagramTimestamp[<<chainID, h>>] > GetChainByID(chainID).counterpartyClientHeights[h] + MaxDelay

\* a conjnction of all invariants
Inv ==
    /\ PacketDatagramsDelay

=============================================================================
\* Modification History
\* Last modified Wed Dec 16 17:41:19 CET 2020 by ilinastoilkovska
\* Created Thu Dec 10 13:44:21 CET 2020 by ilinastoilkovska
