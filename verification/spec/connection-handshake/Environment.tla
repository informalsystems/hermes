---------------------------- MODULE Environment ----------------------------

(***************************************************************************

    This module is part of the TLA+ specification for the IBC Connection
    Handshake protocol (identifier 'ICS3'). This is a high-level spec of ICS3.
    
    This module captures the operators and actions outside of the CH protocol
    itself (i.e., the environment).
    Among others, the environment does the following:
    - creates two instances of ConnectionHandshakeModule,
    - wires these instances together,
    - simulates some malicious behavior by injecting incorrect messages
    - provides the initialization step for ICS3 protocol, concretely a
    "ICS3MsgInit" message, so that the two instances can perform the protocol.
    - updates the clients on each instance periodically, or advances the chain
    of each instance. 

 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences


CONSTANT MaxHeight,     \* Maximum height of any chain in the system.
         MaxBufLen      \* Length (size) of message buffers.


ASSUME MaxHeight > 1
ASSUME MaxBufLen >= 1


VARIABLES
    inBufChainA,    \* A buffer (sequence) for messages inbound to chain A.
    inBufChainB,    \* A buffer for messages inbound to chain B.
    outBufChainA,   \* A buffer for messages outgoing from chain A.
    outBufChainB,   \* A buffer for messages outgoing from chain B.
    storeChainA,    \* The local store of chain A.
    storeChainB,    \* The local store of chain B.
    maliciousEnv    \* If TRUE, environment interferes w/ CH protocol.


(************* ChainAConnectionEnds & ChainBConnectionEnds *****************

    The set of records that each chain can use as a valid local connection
    end. For each chain, this set contains one record, since we are
    modeling a single connection in this specification.
 
 ***************************************************************************)
ChainAConnectionEnds == 
    [
        connectionID : { "connAtoB" },
        clientID : { "clientOnAToB" }
    ]
ChainBConnectionEnds ==
    [
        connectionID : { "connBtoA" },
        clientID : { "clientOnBToA" }
    ]

AllConnectionEnds ==
    ChainAConnectionEnds \union ChainBConnectionEnds

AllClientIDs == 
    { x.clientID : x \in AllConnectionEnds }

AllConnectionIDs ==
    { x.connectionID : x \in AllConnectionEnds }

AllChainIDs ==
    { "chainA", "chainB" }

(* Bundle with variables that chain A has access to. *)
chainAVars == <<inBufChainA,    (* Input message buffer. *)
                outBufChainA,   (* Output message buffer. *)
                storeChainA>>   (* The local chain store. *)

(* Bundle with variables that chain B has access to. *)
chainBVars == <<inBufChainB,    (* Input message buffer. *)
                outBufChainB,   (* Output message buffer. *)
                storeChainB>>   (* Local chain store. *)

(* All variables specific to chains. *)
chainStoreVars == <<storeChainA, storeChainB>>

allVars == <<chainStoreVars, 
             inBufChainA, inBufChainB, 
             outBufChainA, outBufChainB,
             maliciousEnv>>


INSTANCE ICS3Types

chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- inBufChainA,
             outBuf         <- outBufChainA,
             store          <- storeChainA,
             ConnectionIDs  <- { x.connectionID : x \in ChainAConnectionEnds },
             ClientIDs      <- { x.clientID : x \in ChainAConnectionEnds }


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- inBufChainB,
             outBuf         <- outBufChainB,
             store          <- storeChainB,
             ConnectionIDs  <- { x.connectionID : x \in ChainBConnectionEnds },
             ClientIDs      <- { x.clientID : x \in ChainBConnectionEnds }


(***************************************************************************
 Environment actions.
 ***************************************************************************)


(* Environment initialization.

    This action kick-starts the ICS3 protocol by assigning an ICS3MsgInit
    msg to either of the two chains (or both).

    Initially, the environment is non-malicious. The environment starts
    acting maliciously once the connection on both chains transitions out
    of state "UNINIT" (the initials state). It is important to
    initialize the protocol like this, otherwise the env. can provoke a
    deadlock. This can happen with the following sequence of actions:
    
    1. Environment injects a ICS3MsgInit to chain A with the following
    correct parameters:

        localEnd |-> [connectionID |-> "connAtoB",
                      clientID |-> "clientIDChainB"]
        remoteEnd |-> [connectionID |-> "connBtoA",
                       clientID |-> "clientIDChainA"]

    2. Environment injects, maliciously, a ICS3MsgInit to chain B with
    the following parameters:

        localEnd |-> [connectionID |-> "connBtoA",
                      clientID |-> "clientIDChainA"]
        remoteEnd |-> [connectionID |-> "connBtoA",
                       clientID |-> "clientIDChainA"]

    Notice that the localEnd is correct, so chain B will validate and
    process this message; the remoteEnd is incorrect, however, but chain
    B is not able to validate that part of the connection, so it will
    accept it as it is.

    2. Chain A processes the ICS3MsgInit (action HandleInitMsg) and
    updates its store.connection with the parameters from step 1 above.
    At this point, chain A "locks onto" these parameters and will not
    accept any others. Chain A also produces a ICS3MsgTry message.

    3. Chain B processes the ICS3MsgInit (action HandleInitMsg) and
    updates its store.connection with the parameters from step 2 above.
    Chain B "locks onto" these parameters and will not accept any others.
    At this step, chain B produces a ICS3MsgTry message with the local
    parameters from its connection.

    Both chains will be locked on a different set of connection parameters,
    and neither chain will accept their corresponding ICS3MsgTry, hence a
    deadlock. To avoid this problem, we prevent the environment from
    acting maliciously in the preliminary parts of the ICS3 protocol, until
    both chains finish locking on the same set of connection parameters.

 *)
InitEnv ==
    /\ maliciousEnv = FALSE
    /\ \/ /\ inBufChainA \in {<<msg>> : (* ICS3MsgInit to chain A. *)
                        msg \in InitMsgs(ChainAConnectionEnds, ChainBConnectionEnds)}
          /\ inBufChainB = <<>>
       \/ /\ inBufChainB \in {<<msg>> : (* ICS3MsgInit to chain B. *)
                        msg \in InitMsgs(ChainBConnectionEnds, ChainAConnectionEnds)}
          /\ inBufChainA = <<>>
       \/ /\ inBufChainA \in {<<msg>> : (* ICS3MsgInit to both chains. *)
                        msg \in InitMsgs(ChainAConnectionEnds, ChainBConnectionEnds)}
          /\ inBufChainB \in {<<msg>> :
                        msg \in InitMsgs(ChainBConnectionEnds, ChainAConnectionEnds)}
    /\ outBufChainA = <<>>
    /\ outBufChainB = <<>>


(*
    TODO EXPLAIN
 *)
Relay(from, to) ==
    /\ from # <<>>
    /\ Len(to) < MaxBufLen - 1
    /\ to' = Append(to, Head(from))
    /\ from' = Tail(from)


(* Default next (good) action for Environment.

    TODO: should advance the height non-deterministically?

    May change either of the store of chain A or B. 
 *)
GoodNextEnv ==
    \/ /\ chmA!CanAdvance
       /\ \/ chmA!AdvanceChainHeight
          \/ chmA!UpdateClient(storeChainB.latestHeight)
       /\ UNCHANGED<<storeChainB, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>
    \/ /\ chmB!CanAdvance
       /\ \/ chmB!AdvanceChainHeight
          \/ chmB!UpdateClient(storeChainA.latestHeight)
       /\ UNCHANGED<<storeChainA, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>


RelayNextEnv ==
    \/ LET msg == Head(outBufChainA)
           targetHeight == IF MessageTypeIncludesConnProof(msg.type)
                           THEN msg.proofHeight
                           ELSE storeChainA.latestHeight
       IN /\ Relay(outBufChainA, inBufChainB)
            (* TODO: remove following line to fix the deadlock. *)
\*          /\ chmB!UpdateClient(storeChainA.latestHeight)
          /\ \/ chmB!CanAdvance /\ chmB!UpdateClient(targetHeight)
             \/ ~ chmB!CanAdvance /\ UNCHANGED storeChainB
          /\ UNCHANGED<<storeChainA, outBufChainB, inBufChainA>>
    \/ LET msg == Head(outBufChainB)
           targetHeight == IF MessageTypeIncludesConnProof(msg.type)
                           THEN msg.proofHeight
                           ELSE storeChainB.latestHeight
       IN /\ Relay(outBufChainB, inBufChainA)
             (* TODO: remove following line to fix the deadlock. *)
\*          /\ chmA!UpdateClient(storeChainB.latestHeight)
          /\ \/ chmA!CanAdvance /\ chmA!UpdateClient(targetHeight)
             \/ ~ chmA!CanAdvance /\ UNCHANGED storeChainA
          /\ UNCHANGED<<storeChainB, outBufChainA, inBufChainB>>


(* Environment malicious behavior.

    The environment injects a msg. in the buffer of one of the chains. 
    This interferes with the ICS3 protocol by introducing additional
    messages that are usually incorrect.
    
    Without the first constraint, on the "Len(inBufChainA)" and
    "Len(inBufChainB)", Env could fill buffers (DoS attack). This can
    lead to a deadlock, because chains will simply be unable to reply
    to each other.
 *)
MaliciousNextEnv ==
    \/ /\ Len(inBufChainA) < MaxBufLen - 1
       /\ inBufChainA' \in {Append(inBufChainA, arbitraryMsg) : 
            arbitraryMsg \in {msg \in ConnectionHandshakeMessages : 
            msg.type = "ICS3MsgTry"}}
       /\ UNCHANGED inBufChainB
    \/ /\ Len(inBufChainB) < MaxBufLen - 1
       /\ inBufChainB' \in {Append(inBufChainB, arbitraryMsg) :
            arbitraryMsg \in {msg \in ConnectionHandshakeMessages : 
                msg.type = "ICS3MsgTry"}}
\*            arbitraryMsg \in ConnectionHandshakeMessages
\*            /\ arbitraryMsg.type = "ICS3MsgTry"}
       /\ UNCHANGED inBufChainA


(* Environment next action.

TODO: explain the relaying functionality and additional variables.

    There are four possible actions that the environment may perform:

    1. A good step: the environment advances or updates the client on
    one of the two chains.

    2. The environment becomes malicious, as a result of both chains
    advancing past the UNINIT step (i.e., after both chains finished 
    locking on to a set of connection parameters).

    3. A malicious step.

    4. The environment stops acting maliciously.
 *)
NextEnv ==
    \/ /\ GoodNextEnv                               (* A good step. *)
       /\ UNCHANGED maliciousEnv
    \/ /\ RelayNextEnv
       /\ UNCHANGED maliciousEnv
\*    \/ /\ UNCHANGED <<chainAVars, chainBVars, maliciousEnv>>
\*    \/ /\ ~ maliciousEnv                            (* Enable malicious env. *)
\*       /\ storeChainA.connection.state # "UNINIT"
\*       /\ storeChainB.connection.state # "UNINIT"
\*       /\ maliciousEnv' = TRUE
\*       /\ MaliciousNextEnv
\*       /\ UNCHANGED<<chainStoreVars, outBufChainA, outBufChainB>>
\*    \/ /\ maliciousEnv                              (* A malicious step. *)
\*       /\ MaliciousNextEnv
\*       /\ UNCHANGED<<maliciousEnv, chainStoreVars, outBufChainA, outBufChainB>>
\*    \/ /\ maliciousEnv                              (* Disable malicious env. *)
\*       /\ maliciousEnv' = FALSE
\*       /\ UNCHANGED<<chainAVars, chainBVars>>


(* Enables when the connection is open on both chains.

    State predicate signaling that the protocol terminated correctly.
 *)
ICS3ReachTermination ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED allVars


ICS3NonTermination ==
    /\ \/ (~ chmA!CanAdvance /\ storeChainA.connection.state # "OPEN")
       \/ (~ chmB!CanAdvance /\ storeChainB.connection.state # "OPEN")
    /\ UNCHANGED allVars


(******************************************************************************

    Main spec. The system comprises the environment plus the two instances of
    ICS3 modules.

 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID and a client. *)
Init ==
    /\ \E clientA \in InitClients({ x.clientID : x \in ChainAConnectionEnds }) :
            chmA!Init("chainA", clientA)
    /\ \E clientB \in InitClients({ x.clientID : x \in ChainBConnectionEnds }) :
            chmB!Init("chainB", clientB)
    /\ InitEnv


(* The two ICS3 modules and the environment alternate their steps. *)
Next ==
    \/ ICS3ReachTermination
    \/ ICS3NonTermination
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED <<chainBVars, maliciousEnv>> 
    \/ chmB!Next /\ UNCHANGED <<chainAVars, maliciousEnv>>


FairProgress ==
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)
    /\ WF_<<chainAVars, chainBVars>>(RelayNextEnv)
\*    /\ \E m \in ConnectionHandshakeMessages : m = Head(inBufChainA)
\*        => WF_chainAVars(chmA!ProcessMsg(m))
\*    /\ <> ~ maliciousEnv
\*    /\ <> ~ activeEnv
\*    /\ \A height \in 1..MaxHeight : WF_storeChainA(chmA!UpdateClient(height))
\*    /\ \A height \in 1..MaxHeight : WF_storeChainB(chmB!UpdateClient(height))
\*    /\ WF_storeChainA(chmA!AdvanceChainHeight)
\*    /\ WF_storeChainB(chmB!AdvanceChainHeight)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


TypeInvariant ==
    /\ chmA!TypeInvariant
    /\ chmB!TypeInvariant


(* Action ProcessMsg will eventually enable & chainAVars 
    will not be unchanged. *)
MessageLivenessPre ==
    TRUE
\*    /\ \E m \in ConnectionHandshakeMessages : m = Head(inBufChainA)
\*        => <><<chmA!ProcessMsg(m)>>_chainAVars
\*    /\ \E m \in ConnectionHandshakeMessages : m = Head(inBufChainB)
\*        => <><<chmB!ProcessMsg(m)>>_chainBVars


(* Liveness property.
    
    We expect to always reach an OPEN connection on both chains if the following
    conditions hold:
    
    1. eventually, the environment stops being malicious, and
    
    2, 3. both chains can advance with at least 4 more steps (4 is the minimum
    number of steps that are necessary for the chains to reach OPEN).
*)
Termination ==
    []((/\ <> ~ maliciousEnv
     (* TODO: add activeEnv mechanism, to disable GoodNextEnv sub-action. *)
\*        /\ <> ~ activeEnv 
        /\ storeChainA.latestHeight < MaxHeight - 4
        /\ storeChainB.latestHeight < MaxHeight - 4
        /\ MessageLivenessPre)
        => <> (/\ storeChainA.connection.state = "OPEN"
               /\ storeChainB.connection.state = "OPEN"))


(* Safety property.

    If the connections in the two chains are not null, then the
        connection parameters must always match.
 *)
ConsistencyProperty ==
    /\ storeChainA.connection.state # "UNINIT"
    /\ storeChainB.connection.state # "UNINIT"
    => storeChainA.connection.parameters 
        = chmB!FlipConnectionParameters(storeChainB.connection.parameters)


Consistency ==
    [] ConsistencyProperty


=============================================================================
\* Modification History
\* Last modified Wed May 20 16:45:24 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

