# What is a relayer?

A relayer is an off-chain process responsible for relaying IBC datagrams between two or more chains by scanning their states and submitting transactions. 

This is because in the IBC architecture, modules are not directly sending messages to each other over networking infrastructure, but instead they create and store the data to be retrieved and used by a relayer to build the IBC datagrams.

 