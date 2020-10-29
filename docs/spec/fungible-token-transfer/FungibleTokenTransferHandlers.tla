------------------- MODULE FungibleTokenTransferHandlers -------------------

EXTENDS Integers, FiniteSets, Sequences, Bank

CreateOutgoingPacket(denomination, amount, sender, receiver, escrowAccount, vouchers) ==
    LET source == (Len(denomination) = 1) IN
    
    \* update escrow account if source 
    LET updatedEscrowAccount ==
        IF source
        THEN TransferCoins(sender, escrowAccount, denomination, amount)
        ELSE escrowAccount IN
    \* update vouchers if not source         
    LET updatedVouchers ==
        IF ~source
        THEN BurnCoins(sender, vouchers, denomination, amount)
        ELSE vouchers IN
    \* create packet data
    LET data ==
        [
            denomination |-> denomination,
            amount |-> amount,
            sender |-> sender,
            receiver |-> receiver
        ] IN  
     
     
    [packetData |-> data,
     escrowAccount |-> updatedEscrowAccount,
     vouchers |-> updatedVouchers] 

ICS20OnPacketRecv(chainID, chain, packet) ==
    LET data == packet.data IN
    LET srcChannelID == packet.srcChannelID IN
    
    LET source == (Head(data.denomination) = srcChannelID) IN
    
    LET updatedDenomination == Tail(data.denomination) IN
    LET prefixedDenomination == <<packet.dstChainID>> \o data.denomination IN 
    
    \* update escrow account if source
    \* TODO: add error handling and acknowledgements
    LET updatedEscrowAccount == 
        IF source 
        THEN TransferCoins(chain.escrowAccount, data.receiver, updatedDenomination, data.amount) 
        ELSE chain.escrowAccount IN
    
    \* update vouchers if not source
    \* TODO: add error handling and acknowledgements         
    LET updatedVouchers ==
        IF ~source
        THEN MintCoins(data.receiver, prefixedDenomination, data.amount)
        ELSE chain.vouchers IN
    
    [escrowAccount |-> updatedEscrowAccount,
     vouchers |-> updatedVouchers] 
     
     
RefundTokens(chainID, chain, packet) ==
    LET data == packet.data IN
    
    LET source == (Len(data.denomination) = 1) IN
    
    \* update escrow account if source
    LET updatedEscrowAccount == 
        IF source 
        THEN TransferCoins(chain.escrowAccount, data.sender, data.denomination, data.amount) 
        ELSE chain.escrowAccount IN
    
    \* update vouchers if not source
    LET updatedVouchers ==
        IF ~source
        THEN MintCoins(data.sender, data.denomination, data.amount)
        ELSE chain.vouchers IN
             
    [escrowAccount |-> updatedEscrowAccount,
     vouchers |-> updatedVouchers] 

=============================================================================
\* Modification History
\* Last modified Thu Oct 29 20:33:20 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:02:01 CEST 2020 by ilinastoilkovska
