from typing import Optional, Dict, Tuple, Set, FrozenSet, List
from utils.input_setup import get_input_provider, make_input_provider, ZenithProvider
from pynadir.utils.logging import TitledLog


"""
Convergence verification for a given DAG measures 2 things:

- (Expected Set) The set of IRs that are in the DAG but cannot be found in the expected switch
- (Offender Set) The set of IRs that are not in the DAG but are found in _some_ switch

Convrgence is equivalent to both of these sets being empty.
"""
VerificationOutput = Tuple[bool, Tuple[List[Tuple[int, int]], List[Tuple[int, int]]]]


class ConvergenceVerifier:
    def __init__(self, provider: Optional[ZenithProvider] = None):
        # Mapping from current topology to a DAG
        self.topo_2_dag_mapping: Optional[Dict[
            FrozenSet[int],
            Tuple[FrozenSet[int], FrozenSet[Tuple[int, int]]]
        ]] = None
        # Mapping from IR to datapath ID
        self.ir_to_dp_mapping: Optional[Dict[int, int]] = None
        self.flapper_map: Optional[Dict[
            int, Tuple[FrozenSet[int], FrozenSet[Tuple[int, int]]]
        ]] = None

        if provider is not None:
            self.input_provider = provider
            # We _ASSUME_ the relevant collections are already being tracked
            self.is_tracking = True
        else:
            make_input_provider()
            self.input_provider = get_input_provider()
    
    def initiate(self):
        self._set_ir_to_dp_mapping()
        self._set_topo_2_dag_mapping()

    def _set_ir_to_dp_mapping(self):
        if self.ir_to_dp_mapping is None:
            # Get ir association ...
            self.ir_to_dp_mapping = dict()
            ir_docs = list(self.input_provider.nib_read_only_provider.query_document(
                'irs', filter={}
            ))
            for ir_doc in ir_docs:
                self.ir_to_dp_mapping[int.from_bytes(ir_doc['_id'].binary, 'big')] = \
                    ir_doc['dp_id']

    def _set_topo_2_dag_mapping(self):
        if self.topo_2_dag_mapping is None:
            # Get the dags ...
            dag_docs = list(self.input_provider.nib_read_only_provider.query_document(
                'dags', filter={}
            ))
            self.topo_2_dag_mapping = dict()
            for dag_doc in dag_docs:
                nodes = frozenset(int.from_bytes(oid.binary, 'big') for oid in dag_doc['nodes'])
                edges = frozenset((
                    int.from_bytes(edge[0].binary, 'big'),
                    int.from_bytes(edge[1].binary, 'big')
                ) for edge in dag_doc['edges'])
                trigger_set = frozenset(dag_doc['trigger_set'])
                self.topo_2_dag_mapping[trigger_set] = (nodes, edges)

    def verify(self, tcam: Dict[int, Set[int]], down_set: Set[int]) -> VerificationOutput:
        self._set_ir_to_dp_mapping()
        self._set_topo_2_dag_mapping()

        expected_list: List[Tuple[int, int]] = list()
        offender_list: List[Tuple[int, int]] = list()

        # Get the expected DAG
        current_trigger_set = frozenset(down_set)
        nodes, _ = self.topo_2_dag_mapping[current_trigger_set]

        # All IRs for the current DAG, should be in the associated switch
        for ir in nodes:
            dp_id = self.ir_to_dp_mapping[ir]
            if ir not in tcam[dp_id]:
                expected_list.append((dp_id, ir))

        # No switch associated with this DAG should contain an IR that does NOT belong to this DAG
        for dp_id, _tcam in tcam.items():
            if dp_id in current_trigger_set:
                continue
            offending_irs = _tcam.difference(nodes)
            if len(offending_irs) > 0:
                offender_list.extend(map(lambda ir: (dp_id, ir), offending_irs))

        return (len(expected_list) == 0) and (len(offender_list) == 0), expected_list, offender_list

    def verify_and_report(self, tcam: Dict[int, Set[int]], down_set: Set[int]):
        converged, expected_list, offender_list = self.verify(tcam, down_set)
        if converged:
            TitledLog.success("verifier", "The network converged to the correct DAG!", both=True)
        else:
            TitledLog.fail("verifier", "The network has not converged to the correct DAG!", both=True)
            for dp_id, ir in expected_list:
                TitledLog.warning("verifier", f"IR {ir} should be in the TCAM of {dp_id}, but is not!", both=True)
            for dp_id, ir in offender_list:
                TitledLog.warning("verifier", f"DP {dp_id} has the following offending IR in the TCAM: {ir}", both=True)

    # def verify_flapper(self, dag_number: int):
    #     converged = True
    #     self._set_ir_to_dp_mapping()
    #     if self.flapper_map is None:
    #         # Get the dags ...
    #         dag_docs = list(self.input_provider.nib_read_only_provider.query_document(
    #             'dags', filter={}
    #         ))
    #         self.flapper_map = dict()
    #         for i, dag_doc in enumerate(dag_docs):
    #             nodes = frozenset(int.from_bytes(oid.binary, 'big') for oid in dag_doc['nodes'])
    #             edges = frozenset((
    #                                   int.from_bytes(edge[0].binary, 'big'),
    #                                   int.from_bytes(edge[1].binary, 'big')
    #                               ) for edge in dag_doc['edges'])
    #             trigger_set = frozenset(dag_doc['trigger_set'])
    #             assert len(trigger_set) == 0
    #             self.flapper_map[i + 1] = (nodes, edges)

    #     nodes, _ = self.flapper_map[dag_number]

    #     # All IRs for the current DAG, should be in the associated switch
    #     for ir in nodes:
    #         dp_id = self.ir_to_dp_mapping[ir]
    #         if ir not in self.tcam[dp_id]:
    #             TitledLog.warning("verifier", f"IR {ir} should be in the TCAM of {dp_id}, but is not!", both=True)
    #             converged = False

    #     # No switch associated with this DAG should contain an IR that does NOT belong to this DAG
    #     for dp_id, tcam in self.tcam.items():
    #         offending_irs = tcam.difference(nodes)
    #         if len(offending_irs) > 0:
    #             TitledLog.warning("verifier", f"DP {dp_id} has the following offending IRs in the TCAM: {offending_irs}", both=True)
    #             converged = False

    #     if converged:
    #         TitledLog.success("verifier", "The network converged to the correct DAG!", both=True)