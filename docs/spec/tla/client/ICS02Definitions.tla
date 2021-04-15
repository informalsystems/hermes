-------------------------- MODULE ICS02Definitions --------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules, and which are relevant for ICS02.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(************************ TYPE ALIASES FOR SNOWCAT *************************)
(* @typeAlias: CLIENTSTATE = 
    [
        clientID: Str,
        heights: Set(Int)
    ];
*)
(* @typeAlias: CHAINSTORE = 
    [
        height: Int, 
        clientStates: Int -> CLIENTSTATE
    ]; 
*) 
(* @typeAlias: DATAGRAM =
    [
        type: Str,
        clientID: Str,
        height: Int
    ];
*)

(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"} 

nullHeight == 0
nullClientID == "none"

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 

BoundedSeq(S, bound) == UNION {[1..n -> S] : n \in 1..bound}

SetHeights(h1, h2) == {h \in 1..10 : h1 <= h /\ h <= h2}

(****************************** ClientStates *******************************
    A client state is a set of heights 
 ***************************************************************************)
ClientStates(ClientIDs, maxHeight) ==
    [
        clientID : ClientIDs,
        heights : SUBSET(1..maxHeight)
    ] 
    
NullClientState ==
    [
        clientID |-> nullClientID,
        heights |-> {}
    ] 

(******************************** ChainStores ******************************
    A set of chain store records, with fields relevant for ICS02. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.
      
 ***************************************************************************)
ChainStores(NrClients, ClientIDs, maxHeight) ==    
    [
        height : 1..maxHeight,
        clientStates : [1..NrClients -> ClientStates(ClientIDs, maxHeight) \union {NullClientState}]
    ] 

(******************************** Datagrams ********************************)
\* Set of datagrams
Datagrams(ClientIDs, maxHeight) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : 1..maxHeight]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : 1..maxHeight]   

\* Set of client datagrams for a specific set ClientIDs of client IDs.
ClientDatagrams(ClientIDs, Heights) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : Heights]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights]   

\* Null datagram    
NullDatagram == 
    [type |-> "null"] 

(***************************************************************************
 Initial value of a chain store for ICS02
 ***************************************************************************)
\* Initial value of the chain store for ICS02: 
\*      - height is initialized to 1
\*      - the counterparty clients are uninitialized
ICS02InitChainStore(NrClients, ClientIDs) == 
    [
        height |-> 1,
        clientStates |-> [clientNr \in 1..NrClients |-> NullClientState]
    ] 
        
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"
     
\* get the latest height of chainID
\* @type: (CHAINSTORE) => Int;
GetLatestHeight(chain) ==
    chain.height

=========================================================================
\* Modification History
\* Last modified Thu Apr 15 12:17:55 CEST 2021 by ilinastoilkovska
\* Created Tue Oct 06 16:26:25 CEST 2020 by ilinastoilkovska
