# What is a relayer?

A relayer is an off-chain process responsible for relaying IBC datagrams between any two chains by scanning chain states and submitting transactions.

This is because in the IBC architecture, chain modules are not directly sending messages to each other over networking infrastructure, but instead they create and store the data to be retrieved and used by a relayer to build the IBC datagrams.

 