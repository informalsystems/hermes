use flex_error::*;

pub type Error = anyhow::Error;



define_error! {
    #[derive(Debug)]
    ConnectionError {
        InvalidState
        {id: i32}
        | e | { format_args!("connection state unknown") },

        ConnectionExistsAlready
        {connection_id: crate::ics24_host::identifier::ConnectionId}
        | e | { format_args!("connection exists (was initialized) already: {0}", e.connection_id) },

        ConnectionMismatch
        {connection_id: crate::ics24_host::identifier::ConnectionId}
        | e | { format_args!("a different connection exists (was initialized) already for the same connection identifier {0}", e.connection_id) },

        UninitializedConnection
        {connection_id: crate::ics24_host::identifier::ConnectionId}
        | e | { format_args!("connection end for identifier {0} was never initialized", e.connection_id) },

        InvalidConsensusHeight
        {height_left: crate::Height,  height_right: crate::Height}
        | e | { format_args!("consensus height claimed by the client on the other party is too advanced: {0} (host chain current height: {1})", e.height_left, e.height_right) },

        StaleConsensusHeight
        {height_left: crate::Height,  height_right: crate::Height}
        | e | { format_args!("consensus height claimed by the client on the other party has been pruned: {0} (host chain oldest height: {1})", e.height_left, e.height_right) },

        Identifier
        [DisplayError<Error>]
        | _ | { format_args!("identifier error") },

        EmptyProtoConnectionEnd
        | e | { format_args!("ConnectionEnd domain object could not be constructed out of empty proto object") },

        InvalidVersion
        [DisplayError<Error>]
        | _ | { format_args!("invalid version") },

        EmptyVersions
        [DisplayError<Error>]
        | _ | { format_args!("empty supported versions") },

        NoCommonVersion
        | _ | { format_args!("no common version") },

        InvalidAddress
        | _ | { format_args!("invalid address") },

        MissingProofHeight
        | _ | { format_args!("missing consensus proof height") },

        MissingConsensusHeight
        | _ | { format_args!("missing consensus proof height") },

        InvalidProof
        [DisplayError<Error>]
        | _ | { format_args!("invalid connection proof") },

        InvalidSigner
        | _ | { format_args!("invalid signer") },

        ConnectionNotFound
        {connection_id: crate::ics24_host::identifier::ConnectionId}
        | e | { format_args!("no connection was found for the previous connection id provided {0}", e.connection_id) },

        InvalidCounterparty
        | _ | { format_args!("invalid counterparty") },

        ConnectionIdMismatch
        { connection_id_left: crate::ics24_host::identifier::ConnectionId, connection_id_right: crate::ics24_host::identifier::ConnectionId }
        | e | { format_args!("counterparty chosen connection id {0} is different than the connection id {1}", e.connection_id_left, e.connection_id_right) },

        MissingCounterparty
        [DisplayError<Error>]
        | _ | { format_args!("missing counterparty") },

        MissingCounterpartyPrefix
        | _ | { format_args!("missing counterparty prefix") },

        MissingClient
        {client_id: crate::ics24_host::identifier::ClientId}
        | e | { format_args!("the client id does not match any client state: {0}", e.client_id) },

        NullClientProof
        | _ | { format_args!("client proof must be present") },

        FrozenClient
        {client_id: crate::ics24_host::identifier::ClientId}
        | e | { format_args!("the client {0} running locally is frozen", e.client_id) },

        ConnectionVerificationFailure
        | _ | { format_args!("the connection proof verification failed") },

        MissingClientConsensusState
        {height: crate::Height, client_id: crate::ics24_host::identifier::ClientId}
        | e | { format_args!("the consensus state at height {0} for client id {1} could not be retrieved", e.height, e.client_id) },

        MissingLocalConsensusState
        | _ | { format_args!("the local consensus state could not be retrieved") },

        ConsensusStateVerificationFailure
        { height: crate::Height }
        | e | { format_args!("the consensus proof verification failed (height: {0})", e.height) },

        ClientStateVerificationFailure
        { client_id: crate::ics24_host::identifier::ClientId }
        | e | { format_args!("the client state proof verification failed for client id: {0}", e.client_id) },

        Attribute
        [ DisplayError<Error> ]
        |e| { format_args!("{}", e.source) },

        ValidationKind
        [DisplayError<Error>]
        | e | { format_args!("{}", e.source) },
    }
}
