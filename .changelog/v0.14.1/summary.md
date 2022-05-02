This release improves the reliability of the relayer by fixing an edge case where
some queries would fail if they reach a full node after a new block is committed but before the application state updates to reflect the changes in that block.
