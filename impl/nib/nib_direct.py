from warnings import warn
from pynadir.utils.logging import TitledLog
from nib.nib_defs import *
from nib.nib_events import TEEvent, TE_EVENT_TYPE


class NIBDirect(NIBBase):
	"""
	A helper class for tests.
	Clears and then populates the NIB with data so that we can test both it
	and any module that we run on top of it.

	It inserts 3 switches running ofproto 1.3, and then it will upload 8 IRs
	with different states, mapping to different switches.
	Then we create two arbitrary DAGs for them, one when all switches are
	active and one for when SW2 goes down.
	We assume that at present, some IRs for each switch have been scheduled.
	"""
	def __init__(self, path: str = None, db_name: str = 'nib'):
		if path is None:
			super(NIBDirect, self).__init__(db_name=db_name)
		else:
			super(NIBDirect, self).__init__(path, db_name=db_name)

		self.ir_list = None
		self.te_events = None
		self.dags = None
		self.active_dag = None

	def clear_all(self, quiet=False):
		self.client.drop_database(self.db_name)
		self.db = self.client[self.db_name]

		if not quiet:
			TitledLog.warning('nib', f"Cleared {self.db_name} database")

	def clear_collection(self, collection_name):
		self.db.drop_collection(collection_name)

	def insert_ir_and_update_uid(self, ir: IR):
		uid = self.insert_document('ir', ir.get_dict())
		ir.uid = uid

		return uid

	def insert_dag_and_update_uid(self, dag: DAG):
		uid = self.insert_document('dag', dag.get_dict())
		dag.uid = uid

		return uid

	def replace_uid_dag(self, uid_dag: UID_DAG):
		self.replace_one_document(COLLECTIONS.DAG, {'_id': uid_dag.uid})

	def put_te_event(self, event: TEEvent):
		return self.put_on_queue('te_event', event.__dict__)

	def get_te_event_nonblocking(self):
		return self.pop_from_queue('te_event')

	def insert_dps(self, dp_list):
		return self.insert_documents('datapath', [dp.get_dict() for dp in dp_list])

	def put_ir_on_queue(self, ir: IR):
		warn("This form of IR queue message is deprecated", DeprecationWarning, stacklevel=2)
		return self.put_on_queue('ir_queue', {
				'ir': {
					'_id': ir.uid,
					'type': ir.type,
					'command': ir.command,
					'dp_id': ir.dp_id,
					'state': ir.state,
					'target': ir.target
				},
				'tag': -1
			})

	def set_ir_state(self, ir: IR, state: IR_STATE):
		nib_res = self.update_document(COLLECTIONS.IR, {'_id': ir.uid}, {'$set': {'state': state}})
		return nib_res

	def set_switch_state(self, dp_id, state: IR_STATE):
		nib_res = self.update_document(COLLECTIONS.DATAPATH, {'dp_id': dp_id}, {'$set': {'state': state}})
		return nib_res

	def set_sched_set(self, dp_obj, sched_set):
		nib_res = self.update_document(
			COLLECTIONS.DATAPATH, {'dp_id': dp_obj.dp_id}, {'$set': {'sched_ir': [sched.uid for sched in sched_set]}}
		)
		dp_obj.set_sched_ir_set(sched_set)
		return nib_res

	def add_delete_dependency_to_active_dag(self, removable_ir_deletion_uid):
		nib_res = self.update_document(COLLECTIONS.ACTIVE_DAG, {}, {'$push': {'dep': removable_ir_deletion_uid}})
		return nib_res

	def get_deletion_irs(self):
		nib_res = self.query_document(COLLECTIONS.IR, {'type': IR_TYPE.DELETE_FLOW})
		return [IR.parse_from_nib(doc) for doc in nib_res]

	def initiate_failover(self, next_master_identity):
		self.update_document(COLLECTIONS.ROLE, filter={'identity': next_master_identity}, update={
			'$set': {
				'failover_state': FAILOVER_STATE_NIB.FAILOVER_INIT
			}
		})


def prepare(direct):
	ir_list = [
		IR("table=0,priority=0,actions=output:CONTROLLER", 1, state=IR_STATE.IR_DONE),
		IR("table=0,priority=10,ipv4_dst=10.0.0.1,actions=output:1", 2, state=IR_STATE.IR_DONE),
		IR("table=0,priority=10,ipv4_dst=10.0.0.2,actions=output:2", 2, state=IR_STATE.IR_DONE),
		IR("table=0,priority=10,ipv4_dst=10.0.0.3,actions=output:3", 1, state=IR_STATE.IR_DONE),

		IR("table=0,priority=10,eth_type=0x806,actions=outptu:FLOOD", 3, state=IR_STATE.IR_NONE),
		IR("table=0,priority=10,eth_type=0x86cc,actions=output:CONTROLLER", 1, state=IR_STATE.IR_SENT),
		IR("table=0,priority=0,actions=output:CONTROLLER", 1, state=IR_STATE.IR_NONE),
		IR("table=0,priority=10,in_port=1,actions=output:2", 3, state=IR_STATE.IR_NONE),
		IR("table=0,priority=10,in_port=2,actions=output:1", 2, state=IR_STATE.IR_NONE),
	]

	direct.clear_all()

	for ir in ir_list:
		direct.insert_ir_and_update_uid(ir)

	# for all switches up

	dag1 = DAG(ir_list[0:6], [
			(ir_list[0], ir_list[1]),
			(ir_list[0], ir_list[2]),
			(ir_list[1], ir_list[3]),
			(ir_list[2], ir_list[3]),
			(ir_list[3], ir_list[4]),
			(ir_list[3], ir_list[5]),
			(ir_list[3], ir_list[6]),
			(ir_list[2], ir_list[7]),
			(ir_list[2], ir_list[8])
		])

	# for when sw2 goes down ...

	dag2 = DAG([ir_list[0]] + ir_list[3:8], [
			(ir_list[0], ir_list[3]),
			(ir_list[0], ir_list[5]),
			(ir_list[3], ir_list[6]),
			(ir_list[5], ir_list[7]),
			(ir_list[6], ir_list[4]),
			(ir_list[7], ir_list[4])
		])

	te_events = [
		TEEvent(CONTROLLER_MODULES.OFC_WORKER_POOL, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[0].uid, 'state': IR_STATE.IR_SENT}),
		TEEvent(CONTROLLER_MODULES.OFC_MONITORING_SERVER, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[0].uid, 'state': IR_STATE.IR_DONE}),
		TEEvent(CONTROLLER_MODULES.OFC_WORKER_POOL, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[1].uid, 'state': IR_STATE.IR_SENT}),
		TEEvent(CONTROLLER_MODULES.OFC_MONITORING_SERVER, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[1].uid, 'state': IR_STATE.IR_DONE}),
		TEEvent(CONTROLLER_MODULES.OFC_WORKER_POOL, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[2].uid, 'state': IR_STATE.IR_SENT}),
		TEEvent(CONTROLLER_MODULES.OFC_MONITORING_SERVER, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[2].uid, 'state': IR_STATE.IR_DONE}),
		TEEvent(CONTROLLER_MODULES.OFC_WORKER_POOL, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[3].uid, 'state': IR_STATE.IR_SENT}),
		TEEvent(CONTROLLER_MODULES.OFC_MONITORING_SERVER, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[3].uid, 'state': IR_STATE.IR_DONE}),
		TEEvent(CONTROLLER_MODULES.OFC_WORKER_POOL, {'type': TE_EVENT_TYPE.IR_MOD, 'ir': ir_list[5].uid, 'state': IR_STATE.IR_SENT})
	]

	direct.insert_dag_and_update_uid(dag1)
	direct.insert_dag_and_update_uid(dag2)

	for event in te_events:
		direct.put_te_event(event)

	direct.ir_list = ir_list
	direct.te_events = te_events
	direct.dags = [dag1, dag2]

	dps = [
		Datapath(1, SW_STATE.SW_RUN, 4),
		Datapath(2, SW_STATE.SW_RUN, 4),
		Datapath(3, SW_STATE.SW_RUN, 4)
	]

	direct.insert_dps(dps)

	direct.insert_document('active_dag', dag1.get_dict_with_uid())
	direct.active_dag = dag1

	# Deletion IRs ...
	deletion_ir_list = [
		IR("table=0,priority=10,eth_type=0x86cc,actions=output:CONTROLLER", 1, 
			state=IR_STATE.IR_NONE, target=ir_list[5].uid, type=IR_TYPE.DELETE_FLOW),
		IR("table=0,priority=0,actions=output:CONTROLLER", 1, 
			state=IR_STATE.IR_NONE, target=ir_list[6].uid, type=IR_TYPE.DELETE_FLOW),
		IR("table=0,priority=10,in_port=1,actions=output:2", 3,
			state=IR_STATE.IR_NONE, target=ir_list[7].uid, type=IR_TYPE.DELETE_FLOW),
		IR("table=0,priority=10,in_port=2,actions=output:1", 2,
			state=IR_STATE.IR_NONE, target=ir_list[8].uid, type=IR_TYPE.DELETE_FLOW),
	]

	for ir in deletion_ir_list:
		direct.insert_ir_and_update_uid(ir)
		direct.add_delete_dependency_to_active_dag(ir.uid)

	direct.set_sched_set(dps[0], {ir_list[0], ir_list[3], ir_list[5], deletion_ir_list[0]})
	direct.set_sched_set(dps[1], {ir_list[1], ir_list[2]})
	direct.set_sched_set(dps[2], {ir_list[4]})


def insert_irs(direct):
	ir_list = [
		IR("command1", 1),
		IR("command2", 1),
		IR("command3", 1),
		IR("command4", 1),
		IR("command5", 1),
		IR("command1", 2),
		IR("command2", 2),
		IR("command3", 2),
		IR("command4", 2),
		IR("command1", 3),
		IR("command2", 3),
		IR("command3", 3)
	]

	for ir in ir_list:
		direct.insert_ir_and_update_uid(ir)


if __name__ == '__main__':
	direct = NIBDirect()
	prepare(direct)
