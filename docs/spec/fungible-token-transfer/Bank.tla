-------------------------------- MODULE Bank --------------------------------

EXTENDS Integers, FiniteSets

\* subtract coins from account
SubtractCoins(accounts, accountID, amount) ==
    [accounts EXCEPT ![accountID] = accounts[accountID] - amount]

\* add coins to account
AddCoins(accounts, accountID, amount) ==
    LET newDomain == (DOMAIN accounts) \union {accountID} IN
     
    \* if an account with accountID exists
    IF accountID \in DOMAIN accounts
    \* add amount to account
    THEN [accounts EXCEPT ![accountID] = accounts[accountID] + amount]
    \* otherwise create a new account with balance equal to amount 
    \* and add it to the map
    ELSE [accID \in newDomain |-> 
            IF accID = accountID
            THEN amount
            ELSE accounts[accID]   
         ]


\* Transfer coins from senderAccounts to receiverAccounts, depeding on 
\* the sender addressees, receiver addressees and denomination 
\*      - senderAccounts is a map from sender addresses and denominations 
\*        to account balances
\*      - receiverAccounts is a map from receiver addresses and denominations 
\*        to account balances
TransferCoins(senderAccounts, senderAddr, 
              receiverAccounts, receiverAddr, 
              denomination, amount) ==
    LET senderAccountID == <<senderAddr, denomination>> IN
    LET receiverAccountID == <<receiverAddr, denomination>> IN
    
    LET senderBalance == senderAccounts[senderAccountID] IN 
    
    \* if the sender account exists and its balance is sufficient 
    IF /\ senderAccountID \in DOMAIN senderAccounts
       /\ senderBalance - amount >= 0
    \* subtract coins from senderAccountID and add coins to receiverAccountID  
    THEN [
            senderAccounts |-> SubtractCoins(senderAccounts, senderAccountID, amount), 
            receiverAccounts |-> AddCoins(receiverAccounts, receiverAccountID, amount),
            error |-> FALSE
         ]
    \* otherwise report an error         
    ELSE [
            senderAccounts |-> senderAccounts,
            receiverAccounts |-> receiverAccounts,
            error |-> TRUE
         ]
    
    
\* Burn coins on accounts, depending on the address and 
\* denomination  
\*      - accounts is a map from addresses and denominations 
\*        to account balances
BurnCoins(accounts, address, denomination, amount) ==
    LET accountID == <<address, denomination>> IN
    LET balance == accounts[accountID] IN
    
    \* if the account exists and its balance is sufficient 
    IF /\ accountID \in DOMAIN accounts
       /\ balance - amount >= 0
    \* subtract coins from accountID   
    THEN [
            accounts |-> SubtractCoins(accounts, accountID, amount), 
            error |-> FALSE
         ]
    \* otherwise report an error         
    ELSE [
            accounts |-> accounts,
            error |-> TRUE
         ]
    

\* Mint new coins of denomination to account with the given address
MintCoins(accounts, address, denomination, amount, maxBalance) ==
    LET accountID == <<address, denomination>> IN

    \* if the new balance does not exceed maxBalance
    IF \/ /\ accountID \notin DOMAIN accounts
          /\ amount <= maxBalance 
       \/ /\ accountID \in DOMAIN accounts
          /\ accounts[accountID] + amount <= maxBalance
    \* add coins to accountID   
    THEN [
            accounts |-> AddCoins(accounts, accountID, amount), 
            error |-> FALSE
         ]
    \* otherwise report an error         
    ELSE [
            accounts |-> accounts,
            error |-> TRUE
         ]

    

=============================================================================
\* Modification History
\* Last modified Thu Nov 19 18:54:36 CET 2020 by ilinastoilkovska
\* Created Thu Oct 28 19:49:56 CET 2020 by ilinastoilkovska
