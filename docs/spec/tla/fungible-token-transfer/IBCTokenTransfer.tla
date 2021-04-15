------------------------- MODULE IBCTokenTransfer -------------------------

(***************************************************************************
 A TLA+ specification of the IBC Fungible Token Transfer Protocol (ICS20).
 This module is the main module in the specification and models a   
 system of two chains, where each chain perofmrs a transaction that sends 
 1 token to the respective counterparty. 
 
 The specification also contains type annotations for the model checker
 Apalache.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCTokenTransferDefinitions

CONSTANTS 
    \* @type: Int;
    MaxHeight, \* maximal height of all the chains in the system
    \* @type: Int;
    MaxPacketSeq, \* maximal packet sequence number
    \* @type: Int;
    MaxBalance, \* maximal account balance
    \* @type: Str;
    NativeDenominationChainA, \* native denomination of tokens at ChainA
    \* @type: Str;
    NativeDenominationChainB \* native denomination of tokens at ChainA

VARIABLES 
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: CHAINSTORE;
    chainBstore, \* store of ChainB
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainA, \* sequence of packet datagrams incoming to ChainA
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainB, \* sequence of packet datagrams incoming to ChainB
    \* @type: Seq(LOGENTRY);
    packetLog, \* packet log
    \* @type: Int;
    appPacketSeqChainA, \* packet sequence number from the application on ChainA
    \* @type: Int;
    appPacketSeqChainB, \* packet sequence number from the application on ChainB
    \* @type: ACCOUNT -> Int;
    accounts, \* a map from chainIDs and denominations to account balances
    \* @type: ACCOUNT -> Int;
    escrowAccounts \* a map from channelIDs and denominations to escrow account balances

chainAvars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA>>
chainBvars == <<chainBstore, packetDatagramsChainB, appPacketSeqChainB>>
vars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA,
          chainBstore, packetDatagramsChainB, appPacketSeqChainB,
          packetLog, accounts, escrowAccounts>>

Heights == 1..MaxHeight
NativeDenominations == {NativeDenominationChainA, NativeDenominationChainB}   
AllDenominations == Seq(ChannelIDs \union PortIDs \union NativeDenominations)       
          
(***************************************************************************
 Instances of ICS20Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               NativeDenomination <- NativeDenominationChainA,
               chainStore <- chainAstore,
               incomingPacketDatagrams <- packetDatagramsChainA,    
               appPacketSeq <- appPacketSeqChainA    

\* ChainB -- Instance of Chain.tla
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               NativeDenomination <- NativeDenominationChainB,
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
          /\ chainAstore' = [chainAstore EXCEPT 
                            !.counterpartyClientHeights = 
                                chainAstore.counterpartyClientHeights 
                                \union 
                                {chainBstore.height}                          
                          ]
          /\ UNCHANGED chainBstore
       \/ /\ chainID = "chainB"
          /\ chainBstore' = [chainBstore EXCEPT 
                            !.counterpartyClientHeights = 
                                chainBstore.counterpartyClientHeights 
                                \union 
                                {chainAstore.height}                          
                          ]
          /\ UNCHANGED chainAstore
    /\ UNCHANGED <<accounts, escrowAccounts, appPacketSeqChainA, appPacketSeqChainB>>
    /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB, packetLog>>


\* Compute a packet datagram designated for dstChainID, based on the packetLogEntry
\* @type: (Str, Str, LOGENTRY) => DATAGRAM;
PacketDatagram(srcChainID, dstChainID, packetLogEntry) ==
    
    LET srcChannelID == GetChannelID(srcChainID) IN \* "chanAtoB" (if srcChainID = "chainA")
    LET dstChannelID == GetChannelID(dstChainID) IN \* "chanBtoA" (if dstChainID = "chainB")
    
    LET srcPortID == GetPortID(srcChainID) IN \* "portA" (if srcChainID = "chainA")
    LET dstPortID == GetPortID(dstChainID) IN \* "portB" (if dstChainID = "chainB")
    
    LET srcHeight == GetLatestHeight(GetChainByID(srcChainID)) IN
    
    \* the source chain of the packet that is received by dstChainID is srcChainID
    LET recvPacket == [
                        sequence |-> packetLogEntry.sequence, 
                        timeoutHeight |-> packetLogEntry.timeoutHeight,
                        srcChannelID |-> srcChannelID,
                        srcPortID |-> srcPortID,
                        dstChannelID |-> dstChannelID,
                        dstPortID |-> dstPortID,
                        data |-> packetLogEntry.data
                      ] IN
                                 
    \* the source chain of the packet that is acknowledged by srcChainID is dstChainID
    LET ackPacket == [
                        sequence |-> packetLogEntry.sequence, 
                        timeoutHeight |-> packetLogEntry.timeoutHeight,
                        srcChannelID |-> dstChannelID,
                        srcPortID |-> dstPortID,
                        dstChannelID |-> srcChannelID,
                        dstPortID |-> srcPortID,
                        data |-> packetLogEntry.data
                     ] IN  
    
    IF packetLogEntry.type = "PacketSent"
    THEN [
            type |-> "PacketRecv",
            packet |-> recvPacket,
            proofHeight |-> srcHeight
         ]
    ELSE IF packetLogEntry.type = "WriteAck"
         THEN [
                type |-> "PacketAck",
                packet |-> ackPacket,
                acknowledgement |-> packetLogEntry.acknowledgement,  
                proofHeight |-> srcHeight
              ]
         ELSE NullDatagram 
 
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
              /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB>>
           \/ /\ packetDatagram /= NullDatagram 
              /\ srcChainID = "chainA"
              /\ packetDatagramsChainB' = 
                      Append(packetDatagramsChainB, packetDatagram)
              /\ UNCHANGED packetDatagramsChainA
           \/ /\ packetDatagram /= NullDatagram
              /\ srcChainID = "chainB"
              /\ packetDatagramsChainA' = 
                    Append(packetDatagramsChainA, 
                       PacketDatagram(srcChainID, dstChainID, packetLogEntry))
              /\ UNCHANGED packetDatagramsChainB
        
        /\ packetLog' = Tail(packetLog)    
        /\ UNCHANGED <<chainAstore, chainBstore>>
        /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB>>
        /\ UNCHANGED <<accounts, escrowAccounts>>                       
    
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchange
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars

\* EnvironmentAction: create packet datagrams if packet log is not empty       
EnvironmentAction ==
    \/ CreateDatagrams    
    \/ UpdateClients
    
(***************************************************************************
 Specification
 ***************************************************************************)    
               
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    \* bank accounts for each chain ID and its native denomination have MaxBalance
    /\ accounts = 
            [<<chainID, nativeDenom>> \in {<<"chainA", <<NativeDenominationChainA>>>>, 
                                           <<"chainB", <<NativeDenominationChainB>>>>} 
                                           |-> MaxBalance]  
    \* escrow accounts for each channel ID and the chain's native denomination have balance 0                                            
    /\ escrowAccounts = 
            [<<counterpartyChannelID, nativeDenom>> \in {<<"chanBtoA", <<NativeDenominationChainA>>>>, 
                                           <<"chanAtoB", <<NativeDenominationChainB>>>>} 
                                           |-> 0]
    /\ packetLog = <<>>
    
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
    
\* fairness constraint    
Fairness ==
    /\ ChainA!Fairness
    /\ ChainB!Fairness
    /\ WF_vars(Next)    
    
Spec == Init /\ [][Next]_vars /\ Fairness             

(***************************************************************************
 Helper operators used in properties and invariants
 ***************************************************************************)     

RECURSIVE Sum(_)

\* sum of elements in a set
Sum(S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE IN
    x + Sum(S \ {x})
    
\* get the native denomination based on chainID
GetNativeDenomination(chainID) ==
    IF chainID = "chainA"
    THEN NativeDenominationChainA
    ELSE NativeDenominationChainB

\* set of prefixed denominations given a native denomination 
\* @type: (Str) => Set(Seq(Str));    
PrefixedDenoms(nativeDenomination) ==
    {<<portID, channelID, nativeDenomination>> : portID \in PortIDs, channelID \in ChannelIDs}    

\* set of escrow account IDs 
\* @type: Set(<<Str, Seq(Str)>>);
EscrowAccountsDomain ==
    {<<GetCounterpartyChannelID(chainID), <<GetNativeDenomination(chainID)>>>> : 
            chainID \in ChainIDs}    

\* set of all denominations
Denominations ==
    {<<NativeDenominationChainA>>, <<NativeDenominationChainB>>}
    \union
    PrefixedDenoms(NativeDenominationChainA) 
    \union 
    PrefixedDenoms(NativeDenominationChainB)
        
\* create expected packet receipt for a given packet commitment
\* @type: (Str, PACKETCOMM) => [channelID: Str, portID: Str, sequence: Int];
PacketReceipt(chainID, packetCommitment) == 
    [
        channelID |-> GetCounterpartyChannelID(chainID),
        portID |-> GetCounterpartyPortID(chainID),
        sequence |-> packetCommitment.sequence
    ]        
    
\* get the escrow account IDs for the native denomination
\* @type: (Str) => Set(<<Str, Seq(Str)>>);
EscrowAccountIDs(nativeDenomination) == 
    {<<channelID, <<nativeDenomination>>>> : channelID \in ChannelIDs} 

\* a packet is in flight if a packet commitment exists, but a 
\* corresponding packet receipt is not on the counterparty chain    
\* @type: (Str, Str) => Set(Int);
GetAmountsInFlight(chainID, nativeDenom) ==

    \* get packet commitments of chainID and packet receipts of its counterparty
    LET packetCommittments == GetChainByID(chainID).packetCommitments IN
    LET counterpartyChainID == GetCounterpartyChainID(chainID) IN
    LET counterpartyPacketReceipts == GetChainByID(counterpartyChainID).packetReceipts IN
         
    \* get packet commitments for packets in flight
    LET inFlight == {pc \in packetCommittments : 
            PacketReceipt(chainID, pc) \notin counterpartyPacketReceipts} IN
    
    \* get packet data for packets in flight
    LET inFlightData == {pc.data : pc \in inFlight} IN
    
    \* get packet data for packets in flight that have a prefixed denomination,
    \* where the last field is the native denomination of chainID
    LET inFlightDataOfDenomination == {d \in inFlightData : 
            d.denomination[Len(d.denomination)] = nativeDenom} IN
          
    \* compute set of amounts of the packets in flight that have 
    \* the desired denomination          
    {d.amount : d \in inFlightDataOfDenomination}
    
\* compute sum over accounts that have chainID's native denomination
SumOverLocalAccounts(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    \* get counterparty channel ID 
    LET counterpartyChannelID == GetCounterpartyChannelID(chainID) IN
        
    \* compute the sum over bank accounts and escrow accounts with 
    \* native denomination
    accounts[<<chainID, <<nativeDenomination>>>>] +
    escrowAccounts[<<counterpartyChannelID, <<nativeDenomination>>>>]

\* compute the sum over the amounts in escrow accounts
\* @type: (Str) => Int;
SumOverEscrowAccounts(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    
    \* get the escrow account IDs for the native denomination
    LET escrowAccountIDs == EscrowAccountIDs(nativeDenomination) IN
    \* get the amounts in escrow accounts for the native denomination    
    LET escrowAccountAmounts == {escrowAccounts[accountID] : 
            accountID \in (escrowAccountIDs \intersect DOMAIN escrowAccounts)} IN
    
    \* compute the sum over the amounts in escrow accounts
    Sum(escrowAccountAmounts)

\* compute the sum over the amounts of packets in flight
SumOverPacketsInFlight(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN

    \* get the set of amounts of packets in flight for each chain
    LET amountsInFlight == UNION {GetAmountsInFlight(chID, nativeDenomination) : chID \in ChainIDs} IN
    
    \* compute the sum over the amounts of packets in flight
    Sum(amountsInFlight)

\* compute the sum over the amounts in bank accounts for prefixed denomination
SumOverBankAccountsWithPrefixedDenoms(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    
    \* compute the set of prefixed denominations
    LET prefixedDenominations == {pd \in PrefixedDenoms(nativeDenomination) : 
            /\ Len(pd) > 1
            /\ pd[Len(pd)] = nativeDenomination} IN

    \* get the bank account IDs for the prefixed denominations 
    LET accountIDs == {<<chID, prefixedDenomination>> : 
            chID \in ChainIDs, prefixedDenomination \in prefixedDenominations} IN 
               
    \* get the amounts in bank accounts for the prefixed denominations    
    LET accountAmounts == {accounts[accountID] : 
            accountID \in (accountIDs \intersect DOMAIN accounts)} IN
    
    \* compute the sum over the amounts in bank accounts
    Sum(accountAmounts)           

(***************************************************************************
 Properties and invariants
 ***************************************************************************)
 
\* Type invariant
TypeOK ==
    /\ chainAstore \in ChainStores(Heights, MaxPacketSeq, MaxBalance, NativeDenominations)
    /\ chainBstore \in ChainStores(Heights, MaxPacketSeq, MaxBalance, NativeDenominations)
    /\ appPacketSeqChainA \in 1..(MaxPacketSeq + 1)
    /\ appPacketSeqChainB \in 1..(MaxPacketSeq + 1)
    /\ packetDatagramsChainA \in Seq(Datagrams(Heights, MaxPacketSeq, MaxBalance, NativeDenominations))
    /\ packetDatagramsChainB \in Seq(Datagrams(Heights, MaxPacketSeq, MaxBalance, NativeDenominations))
    /\ packetLog \in Seq(PacketLogEntries(Heights, MaxPacketSeq, MaxBalance, NativeDenominations))
    /\ DOMAIN accounts \subseteq ChainIDs \X AllDenominations 
    /\ \A accountID \in DOMAIN accounts : accounts[accountID] \in 0..MaxBalance
    /\ DOMAIN escrowAccounts \subseteq EscrowAccountsDomain
    /\ \A accountID \in DOMAIN escrowAccounts : escrowAccounts[accountID] \in 0..MaxBalance  

\* There are MaxBalance coins of the native denomination in bank and escrow accounts 
\* for a given chain
\* Note: this property still holds if the counterparty chain is malicious 
PreservationOfTotalSupplyLocal ==
    \A chainID \in ChainIDs :
         SumOverLocalAccounts(chainID) = MaxBalance

\* The amount in nativeDenomination in escrow accounts 
\* is equal to the sum of:
\*    * the amounts in-flight packets in a (prefixed or unprefixed) denomination ending 
\*      in nativeDenomination, and
\*    * the amounts in accounts in a prefixed denomination ending in 
\*      nativeDenomination, in which it is not native
\* Note: this property is satisfied only if both chains are correct
PreservationOfTotalSupplyGlobal ==
    \A chainID \in ChainIDs : 
        SumOverEscrowAccounts(chainID) = 
            SumOverPacketsInFlight(chainID) + SumOverBankAccountsWithPrefixedDenoms(chainID)

\* A violation of this property is an execution where fungibility is preserved, 
\* where a return payment is effectuated 
\* Note: this property should also be violated if the counterparty chain is malicious 
\* and effectuates a return payment
NonPreservationOfFungibility ==
    \A accountID \in EscrowAccountsDomain :
        [](escrowAccounts[accountID] > 0 
            => [](escrowAccounts[accountID] > 0))

\* ICS20Inv invariant: conjunction of invariants         
ICS20Inv ==
    /\ PreservationOfTotalSupplyLocal
    /\ PreservationOfTotalSupplyGlobal
    
\* ICS20Prop property: conjunction of properties  
ICS20Prop == 
    NonPreservationOfFungibility    

=============================================================================
\* Modification History
\* Last modified Wed Apr 14 15:24:26 CEST 2021 by ilinastoilkovska
\* Created Mon Oct 17 13:00:24 CEST 2020 by ilinastoilkovska
