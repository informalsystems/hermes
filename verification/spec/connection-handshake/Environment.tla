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
    storeChainB     \* The local store of chain B.


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

ChainAClientIDs ==
    { x.clientID : x \in ChainAConnectionEnds }

ChainBClientIDs ==
    { x.clientID : x \in ChainBConnectionEnds }

ChainAConnectionIDs ==
    { x.connectionID : x \in ChainAConnectionEnds }

ChainBConnectionIDs ==
    { x.connectionID : x \in ChainBConnectionEnds }


(* Bundle with variables that chain A has access to. *)
chainAVars == <<inBufChainA,    (* Input message buffer. *)
                outBufChainA,   (* Output message buffer. *)
                storeChainA>>   (* The local chain store. *)

(* Bundle with variables that chain B has access to. *)
chainBVars == <<inBufChainB,    (* Input message buffer. *)
                outBufChainB,   (* Output message buffer. *)
                storeChainB>>   (* Local chain store. *)

(* All variables specific to both chains. *)
chainStoreVars == <<storeChainA, storeChainB>>

allVars == <<chainStoreVars, 
             inBufChainA, inBufChainB, 
             outBufChainA, outBufChainB>>


(* Separate module with the common type definitions. *)
INSTANCE ICS3Types

chmA == INSTANCE ConnectionHandshakeModule
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- inBufChainA,
             outBuf         <- outBufChainA,
             store          <- storeChainA,
             ConnectionIDs  <- ChainAConnectionIDs,
             ClientIDs      <- ChainAClientIDs


chmB == INSTANCE ConnectionHandshakeModule
        WITH MaxChainHeight <- MaxHeight,
             inBuf          <- inBufChainB,
             outBuf         <- outBufChainB,
             store          <- storeChainB,
             ConnectionIDs  <- ChainBConnectionIDs,
             ClientIDs      <- ChainBClientIDs


(***************************************************************************
 Environment actions.
 ***************************************************************************)


(* Environment initialization.

    This action kick-starts the ICS3 protocol by assigning an ICS3MsgInit
    msg to either of the two chains (or both).

 *)
InitEnv ==
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
    /\ outBufChainA = <<>>  (* Output buffers should be empty initially. *)
    /\ outBufChainB = <<>>


(* Relay sub-action of the environment.

    This performs a basic relaying step, that is, passing a message from the
    output buffer of one of the chains (paramter 'from') into the input buffer
    of another chain (parameter 'to').

 *)
RelayMessage(from, to) ==
    /\ from # <<>>
    /\ Len(to) < MaxBufLen - 1
    /\ to' = Append(to, Head(from))
    /\ from' = Tail(from)


(* Default next action for environment.

    This action may change (non-deterministically) either of the store of chain A
    or B by advancing the height or updating the client on that chain.

 *)
\*DefaultNextEnv ==
\*    \/ /\ chmA!CanAdvance
\*       /\ \/ chmA!AdvanceChainHeight
\*          \/ chmA!UpdateClient(storeChainB.latestHeight)
\*       /\ UNCHANGED<<storeChainB, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>
\*    \/ /\ chmB!CanAdvance
\*       /\ \/ chmB!AdvanceChainHeight
\*          \/ chmB!UpdateClient(storeChainA.latestHeight)
\*       /\ UNCHANGED<<storeChainA, outBufChainA, outBufChainB, inBufChainA, inBufChainB>>


(* Relaying action for the environment.

    This action performs a relaying step: moving a message between the output
    buffer of a chain to the input buffer of the other chain, and updating accordingly
    the client on the latter chain. 

 *)
RelayNextEnv ==
    \/ LET msg == Head(outBufChainA)
           targetHeight == IF MessageTypeIncludesConnProof(msg.type)
                           THEN msg.proofHeight
                           ELSE storeChainA.latestHeight
       IN /\ RelayMessage(outBufChainA, inBufChainB)
            (* TODO: remove following line to fix the deadlock. *)
          /\ chmB!UpdateClient(storeChainA.latestHeight)
          /\ \/ chmB!CanAdvance /\ chmB!CanUpdateClient(targetHeight)
                                /\ chmB!UpdateClient(targetHeight)
             \/ (~ chmB!CanAdvance \/ ~ chmB!CanUpdateClient(targetHeight)) 
\*          /\ \/ chmB!CanAdvance /\ chmB!UpdateClient(targetHeight)
\*             \/ ~ chmB!CanAdvance /\ UNCHANGED storeChainB
          /\ UNCHANGED<<storeChainA, outBufChainB, inBufChainA>>
    \/ LET msg == Head(outBufChainB)
           targetHeight == IF MessageTypeIncludesConnProof(msg.type)
                           THEN msg.proofHeight
                           ELSE storeChainB.latestHeight
       IN /\ RelayMessage(outBufChainB, inBufChainA)
             (* TODO: remove following line to fix the deadlock. *)
          /\ chmA!UpdateClient(storeChainB.latestHeight)
          /\ \/ chmA!CanAdvance /\ chmA!CanUpdateClient(targetHeight)
                                /\ chmA!UpdateClient(targetHeight)
             \/ (~ chmA!CanAdvance \/ ~ chmA!CanUpdateClient(targetHeight))
          /\ UNCHANGED<<storeChainB, outBufChainA, inBufChainB>>


(* Environment next action.

    There are two possible actions that the environment may perform:

    1. A default step: the environment advances or updates the client on
    one of the two chains.

    2. The environment performs a relaying step.

 *)
NextEnv ==
\*    \/ DefaultNextEnv
    \/ RelayNextEnv


(* Enables when the connection is open on both chains.

    State predicate signaling that the protocol terminated correctly.

 *)
ICS3ReachedOpenConnection ==
    /\ storeChainA.connection.state = "OPEN"
    /\ storeChainB.connection.state = "OPEN"
    /\ UNCHANGED allVars


(* Enables when both chains are stuck, i.e., unable to progress while
    their connection is not opened.

    State predicate signaling that the protocol terminated unsucessfully.

 *)
ICS3ImpossibleToAdvance ==
    /\ \/ (~ chmA!CanAdvance /\ storeChainA.connection.state # "OPEN")
       \/ (~ chmB!CanAdvance /\ storeChainB.connection.state # "OPEN")
    /\ UNCHANGED allVars


(******************************************************************************

    Main spec. The system comprises the environment plus the two instances of
    ICS3 modules.

 *****************************************************************************)


(* Initializes both chains, attributing to each a chainID and a client. *)
Init ==
    /\ \E clientA \in InitClients(ChainAClientIDs) :
            chmA!Init("chainA", clientA)
    /\ \E clientB \in InitClients(ChainBClientIDs) :
            chmB!Init("chainB", clientB)
    /\ InitEnv


(* The two ICS3 modules and the environment alternate their steps
    non-deterministically. Eventually, the execution ends with either
    successful (ICS3ReachedOpenConnection sub-action) or unsuccesfull
    (ICS3ImpossibleToAdvance sub-action) termination.
*)
Next ==
    \/ ICS3ReachedOpenConnection
    \/ ICS3ImpossibleToAdvance
    \/ NextEnv
    \/ chmA!Next /\ UNCHANGED chainBVars 
    \/ chmB!Next /\ UNCHANGED chainAVars


FairProgress ==
    /\ WF_chainAVars(chmA!Next)
    /\ WF_chainBVars(chmB!Next)
    /\ WF_<<chainAVars, chainBVars>>(RelayNextEnv)


Spec ==
    /\ Init
    /\ [][Next]_<<allVars>>
    /\ FairProgress


TypeInvariant ==
    /\ chmA!TypeInvariant
    /\ chmB!TypeInvariant


(* Liveness property.

    We expect to always reach an OPEN connection on both chains if the following
    condition holds:
    both chains can advance with at least 4 more steps (4 is the minimum
    number of steps that are necessary for the chains to reach OPEN).
*)
Termination ==
    []((/\ storeChainA.latestHeight < MaxHeight - 4
        /\ storeChainB.latestHeight < MaxHeight - 4)
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
\* Last modified Thu May 21 08:03:07 CEST 2020 by adi
\* Created Fri Apr 24 18:51:07 CEST 2020 by adi

