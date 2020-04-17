--------------------------------- MODULE CH ---------------------------------


\* ----- ASSUMPTIONS -----
\* To be refined and reconsidered as this module evolves:
\*  - there is only 1 relayer and it is correct.
\*  - there are only 2 parties and they are both correct.
\*  - Datagrams are simpler (have less fields) than defined in ICS 033.
\*  - Parties (i.e., each chain) have a fixed, predefined height.
\*  - Relayer is stateless: has no clients, doesn't create proofs.


VARIABLES
    partyState,         \* For each party (A & B), we capture their state. This effectively captures the state of the connection.
    pendingDatagrams    \* Incoming messages to each party; cf. ibc-rs#55
\*    relayerState,       \* Relayer is stateless for the moment. 


NullParty == "none"
Parties == {"chainA", "chainB"}

NullConnectionID == "none"
ConnectionIDs == {"connAtoB", "connBtoA"}

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

Datagrams ==
    [type : {"ConnOpenInit"}, connectionID : ConnectionIDs, counterpartyConnectionID : ConnectionIDs ]
    \union
    [type : {"ConnOpenTry"}, desiredConnectionID : ConnectionIDs, counterpartyConnectionID : ConnectionIDs ]
    \union
    [type : {"ConnOpenAck"}, connectionID : ConnectionIDs ]
    \union
    [type : {"ConnOpenConfirm"}, connectionID : ConnectionIDs ] 
    \union 
    [type : {"NullMsg"} ] \* Unclear if we're going to need this.


\* Helper procedures

\* Would be ideal to import the following two functions, cf. ibc-rs#55 (file: ConnectionHandlers.tla)
getConnectionID(p) ==
    IF p = "chainA"
    THEN "connAtoB"
    ELSE IF p = "chainB"
         THEN "connBtoA"
         ELSE NullConnectionID      

\* get the connection ID of the connection end at chainID's counterparty chain
getCounterpartyConnectionID(p) ==
    IF p = "chainA"
    THEN "connBtoA"
    ELSE IF p = "chainB"
         THEN "connAtoB"
         ELSE NullConnectionID
         
getCounterparty(p) ==
    IF p = "chainA"
    THEN "chainB"
    ELSE IF p = "chainB"
         THEN "chainA"
         ELSE NullParty

isPartyInState(p, state) ==
    partyState[p] = state

    
\*    
\* Helper procedures for constructing datagrams
getInitDatagram(p) ==
    [ type |-> "ConnOpenInit", 
      connectionID |-> getConnectionID(p),
      counterpartyConnectionID |-> getCounterpartyConnectionID(p) ]

getTryDatagram(p) ==
    [ type |-> "ConnOpenTry",
      desiredConnectionID |-> getConnectionID(p),
      counterpartyConnectionID |-> getCounterpartyConnectionID(p) ]


\*
\* Relayer state transitions
    
RelayerSendInit(targetParty) ==
    \* TODO: handle the case where party was already INIT! 
    /\ \A p \in Parties : isPartyInState(p, "UNINIT")   \* Both parties have to be UNINIT
    /\ pendingDatagrams' = [pendingDatagrams EXCEPT
                                ![targetParty] = pendingDatagrams[targetParty] \union { getInitDatagram(targetParty) } 
                           ]
    /\ UNCHANGED <<partyState>>


RelayerSendTry(targetParty) ==
    /\ isPartyInState(targetParty, "UNINIT")
    /\ isPartyInState(getCounterparty(targetParty), "INIT")
    /\ pendingDatagrams' = [pendingDatagrams EXCEPT
                                ![targetParty] = pendingDatagrams[targetParty] \union { getTryDatagram(targetParty) } 
                           ]
    /\ UNCHANGED <<partyState>>

RelayerStep ==
    \E targetParty \in Parties : 
        RelayerSendInit(targetParty)
        \/ RelayerSendTry(targetParty) 
      \*\/ RelayerSendAck \/ RelayerSendConfirm /\ RelayerSendNoMsg



\*
\* Party state transitions

PartyHandleInit(party) ==
    /\ isPartyInState(party, "UNINIT")     \* TODO: allow this handler to be replayed?
    /\ isPartyInState(getCounterparty(party), "UNINIT") \* TODO: can a party read the state of the other party?
    /\ getInitDatagram(party) \in pendingDatagrams[party]
    /\ partyState' = "INIT"
    /\ pendingDatagrams' = [pendingDatagrams EXCEPT     \* inspired from ibc-rs#55
                                ![party] = {}           \* TODO: empty or just \minus the datagram??
                           ]


PartyHandleTry(party) ==
    /\ isPartyInState(party, "UNINIT")     \* TODO: same as for 'PartyHandleInit'.
    /\ isPartyInState(getCounterparty(party), "INIT")
    /\ getTryDatagram(party) \in pendingDatagrams[party]
    /\ partyState' = "INIT"
    /\ pendingDatagrams' = [pendingDatagrams EXCEPT
                                ![party] = {}
                           ]

PartyStep(p) ==
    \E party \in Parties : 
        PartyHandleInit(party)
        \/ PartyHandleTry(party)


\* The initial predicate defining the CH protocol.
Init ==
    \* Associate to each party & relayer an initial state.
    /\ partyState = [ p \in Parties |-> "UNINIT" ]
    /\ pendingDatagrams = {}
    
Next == 
    \/ RelayerStep
    \/ \E p \in Parties : PartyStep(p) 

Spec ==
    Init /\ [][Next]_<<partyState, pendingDatagrams>>


=============================================================================
\* Modification History
\* Last modified Fri Apr 17 12:47:34 CEST 2020 by adi
\* Created Fri Apr 17 10:28:22 CEST 2020 by adi

