import argparse
from itertools import groupby, chain, combinations
from typing import Dict, FrozenSet, Tuple, List, Union, Optional, Generator
from dataclasses import dataclass
from bson.objectid import ObjectId
from pynadir.structures import NadirUID
from pynadir.utils.logging import TitledLog
from nib.nib_direct import NIBDirect


"""
Utility for just setting up dummy IRs for tests and
debugging.

By running this, you can initiate the external 'nib'
database that will contain the user provided IRs, datapaths, 
and DAGs.
"""


def powerset_gen(ls: List) -> Generator:
    for res in chain.from_iterable(combinations(ls, r) for r in range(len(ls)+1)):
        yield res


class NadirIR:
    def __init__(self, command: str, dp_id: int, cookie: int, bson_id: ObjectId = None, nadir_uid: NadirUID = None) -> None:
        self.command = command
        self.dp_id = dp_id
        self.cookie = cookie
        self.bson_id = bson_id
        self.nadir_uid = nadir_uid
    
    def __str__(self) -> str:
        return f"FLOW = {self.cookie} | DP = {self.dp_id} | CMD = {self.command}"
    
    def __eq__(self, value: object) -> bool:
        if isinstance(value, NadirIR):
            if self.nadir_uid and value.nadir_uid and (self.nadir_uid == value.nadir_uid):
                return True
            elif self.bson_id and value.bson_id and (self.bson_id == value.bson_id):
                return True
            elif self.command == value.command and \
                self.dp_id == value.dp_id and \
                self.cookie == value.cookie:
                return True
            return False
        elif isinstance(value, NadirUID):
            return self.nadir_uid == value
        return False
    
    def __hash__(self) -> int:
        # A hash can only exist if the bson_id is known
        return int.from_bytes(self.bson_id.binary, 'big')
    
    def as_dict(self, with_id: bool) -> Dict:
        if with_id:
            assert self.bson_id is not None
            return {
                "command": self.command,
                "dp_id": self.dp_id,
                "cookie": self.cookie,
                "_id": self.bson_id
            }
        return {
            "command": self.command,
            "dp_id": self.dp_id,
            "cookie": self.cookie
        }
    
    def set_bson_id(self, bson_id: ObjectId):
        assert self.bson_id is None
        self.bson_id = bson_id

    def set_nadir_uid(self, nadir_uid: NadirUID):
        assert self.nadir_uid is None
        self.nadir_uid = nadir_uid
    
    def get_bson_id(self) -> ObjectId:
        assert self.bson_id is not None
        return self.bson_id

    @classmethod
    def from_dict(cls, _dict: Dict):
        return cls(
            command=_dict["command"],
            dp_id=_dict["dp_id"],
            cookie=_dict["cookie"],
            bson_id=_dict.get("bson_id"),
            nadir_uid=_dict.get("nadir_uid")
        )


class NadirDAG:
    def __init__(self, nodes: Union[List[NadirIR], FrozenSet[NadirIR]],
                 edges: Union[List[Tuple[NadirIR, NadirIR]], FrozenSet[Tuple[NadirIR, NadirIR]]],
                 trigger_set: FrozenSet[int], bson_id: ObjectId = None) -> None:

        """
        In case the `NadirIR` instances are not ready fully (i.e. they don't yet have
        OIDs), then casting them into a `frozenset` will fail, since they are not yet
        hashable.
        When IRs are ready, the user will call `freeze` on the DAG to prepare it, but
        until then, IRs and edges are kept in a simple list.
        """

        if isinstance(nodes, list):
            assert isinstance(edges, list)
            self._nodes = nodes
            self._edges = edges
            self.nodes = None
            self.edges = None
            self._frozen = False
        else:
            assert isinstance(nodes, frozenset) and isinstance(edges, frozenset)
            self.nodes = nodes
            self.edges = edges
            self._frozen = True

        self.trigger_set = trigger_set
        self.bson_id = bson_id

    def set_bson_id(self, bson_id: ObjectId):
        assert self.bson_id is None
        self.freeze()
        self.bson_id = bson_id

    def get_bson_id(self) -> ObjectId:
        assert self.bson_id is not None
        assert self._frozen
        return self.bson_id

    def freeze(self):
        if not self._frozen:
            self.nodes = frozenset(self._nodes)
            self.edges = frozenset(self._edges)
            del self._nodes
            del self._edges
            self._frozen = True
    
    def as_dict(self, with_ids: bool):
        self.freeze()
        if with_ids:
            return {
                "nodes": [node.bson_id for node in self.nodes],
                "edges": [(t[0].bson_id, t[1].bson_id) for t in self.edges],
                "trigger_set": list(self.trigger_set)
            }
        return {
            "nodes": [node.as_dict(False) for node in self.nodes],
            "edges": [(t[0].as_dict(False), t[1].as_dict(False)) for t in self.edges],
            "trigger_set": list(self.trigger_set)
        }
    
    def as_full_dict(self, with_ids: bool):
        assert self.bson_id is not None
        self.freeze()
        if with_ids:
            return {
                "_id": self.bson_id,
                "nodes": [node.bson_id for node in self.nodes],
                "edges": [(t[0].bson_id, t[1].bson_id) for t in self.edges],
                "trigger_set": list(self.trigger_set)
            }
        return {
            "_id": self.bson_id,
            "nodes": [node.as_dict(False) for node in self.nodes],
            "edges": [(t[0].as_dict(False), t[1].as_dict(False)) for t in self.edges],
            "trigger_set": list(self.trigger_set)
        }
    
    @classmethod
    def from_dict(cls, _dict: Dict):
        return cls(
            nodes=frozenset(_dict["nodes"]),
            edges=frozenset([tuple(ls) for ls in _dict["edges"]]), # noqa
            trigger_set=frozenset(_dict["trigger_set"])
        )

    def get_cookies(self):
        dp_ids = [ir.dp_id for ir in self.nodes]
        cookies = [ir.cookie for ir in self.nodes]
        return {
            dp_id: set(item[1] for item in switch_cookies) for dp_id, switch_cookies in groupby(zip(dp_ids, cookies), lambda item: item[0])
        }


"""
The following is a more general function for setting up IRs and
DAGs.
"""

@dataclass
class NIBSetupParams:
    """
    Describe the NIB (i.e. external data that ZENITH will consume).
    This accepts an arbitrary list of IRs, DAGs and datapaths.
    This is the most generic way to populate the NIB database and
    give inputs to ZENITH.

    Note that there are specification inputs that are not listed
    here, this instance does NOT describe all the input that ZENITH
    needs. See `input_setup.py` for the rest.
    """
    irs: List[NadirIR]
    dags: List[NadirDAG]
    datapaths: Optional[List[int]] = None


@dataclass
class NIBSizeParams:
    """
    Can be used as a shortcut for populating NIB for debugging or
    testing ZENITH.
    This just describes how big the NIB is (i.e. how many IRs,
    switches there are and how big is each DAG) and just creates
    arbitrary instructions.
    This by default MUST be used with the fake frontend and fake 
    switches, since it is not generating things that make sense
    in OpenFlow.
    TODO: Maybe we can fix the above? There is nothing stopping
          us from making stupid OpenFlow messages as long as they
          are well-formed.
    """
    num_switches: int
    num_irs: int
    dag_size: int


def simple_setup(direct: NIBDirect = None, with_datapaths: bool = False, clear_nadir: bool = False) -> NIBSetupParams:
    """
    The simples setup for testing that ZENITH at least works.
    Just 2 switches, 2 really small DAGs with minimum number of IRs.
    The first DAG is for a healthy network and the second for when the
    first datapath becomes unavailable.
    """
    if direct is None:
        direct = NIBDirect()

    # First, clear the NIB
    direct.clear_all()

    if clear_nadir:
        _direct = NIBDirect(db_name='Nadir')
        _direct.clear_all()

    irs = [
        NadirIR("table=0,ip,actions=output:1", 1, 1, bson_id=ObjectId((1).to_bytes(12, 'big'))),
        NadirIR("table=0,ip,actions=output:1", 2, 2, bson_id=ObjectId((2).to_bytes(12, 'big'))),
        NadirIR("table=0,ip,actions=output:1", 2, 3, bson_id=ObjectId((3).to_bytes(12, 'big')))
    ]

    for ir in irs:
        direct.insert_document('irs', ir.as_dict(True))
    
    dag1 = NadirDAG(
        frozenset([irs[0], irs[1]]),
        frozenset([(irs[0], irs[1])]),
        frozenset(),
        bson_id=ObjectId((1).to_bytes(12, 'big'))
    )
    dag2 = NadirDAG(
        frozenset([irs[2]]),
        frozenset(),
        frozenset([1]),
        bson_id=ObjectId((2).to_bytes(12, 'big'))
    )

    direct.insert_document("dags", dag1.as_dict(True))
    direct.insert_document("dags", dag2.as_dict(True))

    if with_datapaths:
        dps = setup_dummy_datapaths(2)
    else:
        dps = None

    return NIBSetupParams(irs=irs, dags=[dag1, dag2], datapaths=dps)


def setup_nib(params: NIBSetupParams, ir_have_id: bool = False, dags_have_id: bool = False, clear_nadir: bool = False):
    """
    Given a `NIBSetupParams` instance, this populates the NIB and setsup any input needed for
    ZENITH core to function.
    
    Parameters
    ----------
    params: NIBSetupParams
        Instance of `NIBSetupParams` that contains all IRs, DAGs and datpaths.
    ir_have_id: bool
        If True, it means that IRs have already been uploaded to the NIB and
        have legitimate ObjectIDs, so we will not change them and just reference
        them in NIB.
    dag_have_id: bool
        Same as above, but for DAGs.
    clear_nadir: bool
        If True, will completely clear the NIB before uploading.
    """
    nib = NIBDirect(db_name='nib')
    nib.clear_all()

    if clear_nadir:
        nadir = NIBDirect(db_name='Nadir')
        nadir.clear_all()

    if ir_have_id:
        ir_dicts = [ir.as_dict(True) for ir in params.irs]
    else:
        ir_dicts = []
        for i, ir in enumerate(params.irs):
            ir.set_bson_id(ObjectId((i+1).to_bytes(12, 'big')))
            ir_dicts.append(ir.as_dict(True))
    nib.insert_documents('irs', ir_dicts, ordered=False)

    if dags_have_id:
        dag_dicts = [dag.as_full_dict(True) for dag in params.dags]
    else:
        dag_dicts = []
        for i, dag in enumerate(params.dags):
            dag.set_bson_id(ObjectId((i+1).to_bytes(12, 'big')))
            dag_dicts.append(dag.as_full_dict(True))
    nib.insert_documents('dags', dag_dicts, ordered=False)
    
    TitledLog.info("ir-setup", f"Inserted {len(params.irs)} IRs and {len(params.dags)} DAGs")


def setup_dummy_datapaths(num: int) -> List[int]:
    """
    Utility function for just setting up dummy datapaths.
    Since the `ZENITH` specifciation only needs a unique reference
    to the datapath, this can work even for real switches.

    Parameters
    ----------
    num: int
        Number of datapaths to insert into NIB
    
    Returns
    -------
    List[int]
        List of datapath IDs that were inserted
    """
    nib = NIBDirect(db_name='nib')
    dps = [{'dp_id': i, '_id': ObjectId((i).to_bytes(12, 'big'))} for i in range(1, num+1)]
    nib.insert_documents(collection='datapaths', documents=dps, ordered=False)
    nib.create_unique_index('datapaths', 'dp_id')

    return list(range(1, num+1))


# def setup_big(switch_count: int = 500, ir_per_dag: int = 1000, total_ir_count: int = 100000):
def setup_big(size_params: NIBSizeParams) -> NIBSetupParams:
    """
    Utility to initiate a NIB of arbitrary size filled with arbitrary data.
    We use this for benchmarking and seeing how much throughput the generated
    ZENITH code has.

    Parameters
    ----------
    size_params: NIBSizeParams
        Instance of `NIBSizeParams` that basically says how many things should
        be in NIB.
    
    Returns
    -------
    NIBSetupParams
        Instance of `NIBSetupParams` that contains all the generated IRs and DAGs.
        These are _guaranteed_ to have valid ObjectIDs on NIB.
    
    Notes
    -----
    This function will generate DAGs for _any_ set of down switches. This means
    that the number of DAGs scales exponentially with number of switches.
    To make life for ZENITH more difficult, these DAGs also do not overlap (i.e.
    each IR is unique to just one DAG).
    So don't be surprised if this function fries the NIB.
    """
    ir_per_dag = size_params.dag_size
    down_switch_gen = powerset_gen([i for i in range(1, size_params.num_switches + 1)])
    total_switch_set = frozenset(range(1, size_params.num_switches + 1))

    irs = []
    dags = []

    # cookie = 1
    # for i in range(size_params.num_irs // ir_per_dag):
    #     down_set = frozenset(next(down_switch_gen))
    #     up_set = list(total_switch_set.difference(down_set))
    #     nodes = [NadirIR(f"table=0,in_port={cookie+j},actions=output:{cookie+j+1}",
    #                      up_set[j % len(up_set)], cookie + j) for j in range(ir_per_dag)]
    #     dags.append(NadirDAG(
    #         nodes=nodes, trigger_set=down_set,
    #         edges=[(nodes[0], nodes[j]) for j in range(1, ir_per_dag)]
    #     ))
    #     irs.extend(nodes)
    cookie = 1
    for i in range(size_params.num_irs // ir_per_dag):
        down_set = frozenset(next(down_switch_gen))
        up_set = list(total_switch_set.difference(down_set))
        nodes = [NadirIR(f"table=0,in_port={cookie+j},actions=output:{cookie+j+1}",
                         up_set[j % len(up_set)], cookie + j) for j in range(ir_per_dag)]
        dags.append(NadirDAG(
            nodes=nodes, trigger_set=down_set,
            edges=[(nodes[0], nodes[j]) for j in range(1, ir_per_dag)]
        ))
        cookie += ir_per_dag
        irs.extend(nodes)

    params = NIBSetupParams(
        irs=irs,
        dags=dags
    )

    setup_nib(params, dags_have_id=False)
    setup_dummy_datapaths(size_params.num_switches)

    return params


if __name__ == '__main__':
    parser = argparse.ArgumentParser("Setup initial NIB database with IRs, DAGs and (possibly) dummy switches")
    parser.add_argument('--num-irs', type=int, help='Number of IRs to generate')
    parser.add_argument('--dag-size', type=int, help='Number of IRs per DAG')
    parser.add_argument('--topo-size', type=int, help='Number of switches')

    args = parser.parse_args()
    if args.num_irs is not None or args.dag_size is not None or args.topo_size is not None:
        assert args.num_irs is not None and args.dag_size is not None and args.topo_size is not None
        size_params = NIBSizeParams(args.topo_size, args.num_irs, args.dag_size)
        setup_big(size_params)
    else:
        direct = NIBDirect()
        simple_setup(direct)
