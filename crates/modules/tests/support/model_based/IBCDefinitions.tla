--------------------------- MODULE IBCDefinitions -----------------------------

EXTENDS Integers, FiniteSets, TLC

(********************** TYPE ANNOTATIONS FOR APALACHE ************************)

\* @typeAlias: CHAIN_ID = Str;
\* @typeAlias: CLIENT_ID = Int;
\* @typeAlias: CONNECTION_ID = Int;
\* @typeAlias: HEIGHT = [ revision_number: Int, revision_height: Int ];
\* @typeAlias: CLIENT = [ heights: Set(HEIGHT) ];
\* @typeAlias: CLIENTS = CLIENT_ID -> CLIENT;
\*
\* @typeAlias: CONNECTION = [ state: Str, chainId: CHAIN_ID, clientId: CLIENT_ID,
\*   connectionId: CONNECTION_ID, counterpartyChainId: CHAIN_ID,
\*   counterpartyClientId: CLIENT_ID, counterpartyConnectionId: CONNECTION_ID ];
\* @typeAlias: CONNECTIONS = CONNECTION_ID -> CONNECTION;
\*
\* @typeAlias: ACTION = [ type: Str, chainId: CHAIN_ID, clientState: HEIGHT, consensusState: HEIGHT,
\*   clientId: CLIENT_ID, header: HEIGHT, previousConnectionId: Int, counterpartyChainId: CHAIN_ID,
\*   counterpartyClientId: CLIENT_ID, counterpartyConnectionId: Int];
\*
\* @typeAlias: CHAIN = [ height: HEIGHT, clients:  CLIENTS, clientIdCounter: Int,
\*   connections: CONNECTIONS, connectionIdCounter: Int, connectionProofs: Set(ACTION) ];
\* @typeAlias: CHAINS = CHAIN_ID -> CHAIN;
\* 
Typedefs == TRUE



(******************* END OF TYPE ANNOTATIONS FOR APALACHE ********************)

(******************************** Utils **************************************)
\* This is an implementation of the height comparison for Tendermint heights,
\* which include a revision (client version) and a block height.
\* - If height x's revision is higher than y's, x is higher.
\* - If x's revision is lower than y's, x is lower
\* - If x and y's revision's are equal, then we look at the block number
\* - - If x's block number is higher, x is higher.
\* - - If x's block number is lower, x is lower.
\* - - If x and y have the same revision and block number, the heights are equal.
\* @type: (HEIGHT, HEIGHT) => Bool;
HeightLT(a, b) ==
    \/ a.revision_number < b.revision_number
    \/ (a.revision_number = b.revision_number /\ a.revision_height < b.revision_height)

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightLTE(a, b) ==
    \/ a.revision_number < b.revision_number
    \/ (a.revision_number = b.revision_number /\ a.revision_height < b.revision_height)
    \/ a = b

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightGT(a, b) ==
    \/ a.revision_number > b.revision_number
    \/ (a.revision_number = b.revision_number /\ a.revision_height > b.revision_height)

\* @type: (HEIGHT, HEIGHT) => Bool;
HeightGTE(a, b) ==
    \/ a.revision_number > b.revision_number
    \/ (a.revision_number = b.revision_number /\ a.revision_height > b.revision_height)
    \/ a = b

\* Checks if the block is higher but the revision is the same
\* @type: (HEIGHT, HEIGHT) => Bool;
HigherRevisionHeight(a, b) ==
    /\ a.revision_number = b.revision_number
    /\ a.revision_height > b.revision_height

\* Checks if the revision is higher
\* @type: (HEIGHT, HEIGHT) => Bool;
HigherRevisionNumber(a, b) ==
    /\ a.revision_number > b.revision_number

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

\* @type: (Set(HEIGHT)) => HEIGHT;
FindMaxHeight(S) == CHOOSE x \in S: \A y \in S: HeightLTE(y, x)

(*****************************************************************************)

\* if a chain identifier is not set then it is "-1"
ChainIdNone == "-1"
\* if a client identifier is not set then it is -1
ClientIdNone == -1
\* if a connection identifier is not set then it is -1
ConnectionIdNone == -1

===============================================================================
