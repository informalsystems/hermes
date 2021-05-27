#[derive(Debug)]
pub enum MetricUpdate {
    RelayChainsNumber(u64),
    RelayChannelsNumber(u64),
    TxCount(u64),
    TxSuccess(u64),
    TxFailed(u64),
    IbcAcknowledgePacket(u64),
    IbcRecvPacket(u64),
    IbcTransferSend(u64),
    IbcTransferReceive(u64),
    TimeoutPacket(u64),
    IbcClientMisbehaviour(u64),
}
