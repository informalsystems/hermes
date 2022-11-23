from typing import Optional, Tuple

from .cmd import *
from .common import *


@dataclass
class ClientCreated:
    client_id: ClientId
    client_type: ClientType
    consensus_height: Height


@dataclass
@cmd("create client")
class TxCreateClient(Cmd[ClientCreated]):
    dst_chain_id: ChainId
    src_chain_id: ChainId

    def args(self) -> List[str]:
        return ["--host-chain", self.dst_chain_id, "--reference-chain", self.src_chain_id]

    def process(self, result: Any) -> ClientCreated:
        return from_dict(ClientCreated, result['CreateClient'])


# -----------------------------------------------------------------------------


@dataclass
class ClientUpdated:
    client_id: ClientId
    client_type: ClientType
    consensus_height: Height


@dataclass
@cmd("update client")
class TxUpdateClient(Cmd[ClientUpdated]):
    dst_chain_id: ChainId
    dst_client_id: ClientId

    def args(self) -> List[str]:
        return ["--host-chain", self.dst_chain_id, "--client", self.dst_client_id]

    def process(self, result: Any) -> ClientUpdated:
        return from_dict(ClientUpdated, result[-1]['UpdateClient']['common'])


# -----------------------------------------------------------------------------

@dataclass
class AllowUpdate:
    after_expiry: bool
    after_misbehaviour: bool


@dataclass
class ClientState:
    chain_id: ChainId
    frozen_height: Optional[Height]
    latest_height: Height
    max_clock_drift: Duration
    trust_threshold: TrustThreshold
    trusting_period: Duration
    unbonding_period: Duration
    upgrade_path: List[str]
    allow_update: AllowUpdate


@dataclass
@cmd("query client state")
class QueryClientState(Cmd[ClientState]):
    chain_id: ChainId
    client_id: ClientId
    height: Optional[int] = None
    proof: bool = False

    def args(self) -> List[str]:
        args = []

        if self.height is not None:
            args.extend(['--height', str(self.height)])
        if self.proof:
            args.append('--proof')

        args.extend(["--chain", self.chain_id, "--client", self.client_id])

        return args

    def process(self, result: Any) -> ClientState:
        return from_dict(ClientState, result)

# =============================================================================
# CLIENT creation and manipulation
# =============================================================================


def create_client(c: Config, dst: ChainId, src: ChainId) -> ClientCreated:
    cmd = TxCreateClient(dst_chain_id=dst, src_chain_id=src)
    client = cmd.run(c).success()
    l.info(f'Created client: {client.client_id}')
    return client


def update_client(c: Config, dst: ChainId, client_id: ClientId) -> ClientUpdated:
    cmd = TxUpdateClient(dst_chain_id=dst,
                         dst_client_id=client_id)
    res = cmd.run(c).success()
    l.info(f'Updated client to: {res.consensus_height}')
    return res


def query_client_state(c: Config, chain_id: ChainId, client_id: ClientId) -> Tuple[ClientId, ClientState]:
    cmd = QueryClientState(chain_id, client_id)
    res = cmd.run(c).success()
    l.debug(f'State of client {client_id} is: {res}')
    return client_id, res


def create_update_query_client(c: Config, dst: ChainId, src: ChainId) -> ClientId:
    client = create_client(c, dst, src)
    split()
    query_client_state(c, dst, client.client_id)
    split()
    update_client(c, dst, client.client_id)
    split()
    query_client_state(c, dst, client.client_id)
    split()
    return client.client_id
