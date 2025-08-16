import json
from typing import Dict
from bson import json_util
from nib.nib_defs import CONTROLLER_MODULES, short_uid, IR


class TE_EVENT_TYPE:
	TOPO_MOD = "TOPO_MOD"
	IR_MOD = "IR_MOD"
	IR_ADD = "IR_ADD"
	IR_REM = "IR_REM"
	TOPO_EXP = "TOPO_EXP"
	TOPO_RED = "TOPO_RED"
	FO_RESET = "FO_RESET"


class DAG_EVENT_TYPE:
	DAG_STALE = "DAG_STALE"
	DAG_NEW = "DAG_NEW"


class NIBEventBase:
	def __init__(self, event_src: CONTROLLER_MODULES, msg):
		if isinstance(event_src, str):
			event_src = CONTROLLER_MODULES[event_src]
		self.event_src = event_src
		self.msg = msg

	def __str__(self):
		return f"FROM {self.event_src} ==> {self.msg}"

	@classmethod
	def parse_from_nib(cls, nib_event):
		return cls(nib_event['event_src'], nib_event['msg'])


class TEEvent(NIBEventBase):
	def __init__(self, *args, **kwargs):
		"""
		For TOPO_MOD:
			msg. type = TOPO_MOD
			msg. sw = dp_id of switch
			msg. state = state of the switch

		For IR_MOD:
			msg. type = IR_MOD
			msg. ir = the ID of an IR
			msg. state = state of the IR

		For IR_ADD:
			msg. type = IR_ADD
			msg. ir = the ID of the new IR
			msg. sw = dp_id of the destination switch

		For IR_REM:
			msg. type = IR_REM
			msg. ir = the ID of the IR to remove from consideration

		For TOPO_EXP:
			msg. type = TOPO_EXP
			msg. sw = dp_id of switch

		For TOPO_RED:
			msg. type = TOPO_RED
			msg. sw = dp_id of switch

		For FO_RESET:
			msg. type = FO_RESET
		"""
		super(TEEvent, self).__init__(*args, **kwargs)

	def __str__(self):
		if self.msg['type'] == TE_EVENT_TYPE.TOPO_MOD:
			return f"Topology Modification | {self.msg['sw']} --> {self.msg['state']}"
		elif self.msg['type'] == TE_EVENT_TYPE.IR_MOD:
			return f"IR Modification | {short_uid(self.msg['ir'])} --> {self.msg['state']}"
		elif self.msg['type'] == TE_EVENT_TYPE.IR_ADD:
			return f"IR Addition | {short_uid(self.msg['ir'])} | DP ID = {self.msg['sw']}"
		elif self.msg['type'] == TE_EVENT_TYPE.IR_REM:
			return f"IR Removal | {short_uid(self.msg['ir'])}"
		elif self.msg['type'] == TE_EVENT_TYPE.TOPO_EXP:
			return f"Topology Expansion | DP ID = {self.msg['sw']}"
		elif self.msg['type'] == TE_EVENT_TYPE.TOPO_RED:
			return f"Topology Reduction | DP ID = {self.msg['sw']}"
		elif self.msg['type'] == TE_EVENT_TYPE.FO_RESET:
			return "FO Reset Event"

	def __eq__(self, other):
		if isinstance(other, TEEvent):
			if other.msg['type'] == TE_EVENT_TYPE.TOPO_MOD:
				return other.msg['sw'] == self.msg['sw'] and other.msg['state'] == self.msg['state']
			if other.msg['type'] == TE_EVENT_TYPE.IR_MOD:
				return other.msg['ir'] == self.msg['ir'] and other.msg['state'] == self.msg['state']
			if other.msg['type'] == TE_EVENT_TYPE.TOPO_EXP:
				return other.msg['sw'] == self.msg['sw']
			if other.msg['type'] == TE_EVENT_TYPE.TOPO_RED:
				return other.msg['sw'] == self.msg['sw']
		return False

	def serialize(self):
		if self.msg['type'] == TE_EVENT_TYPE.IR_MOD:
			return json.dumps({
				'event_src': str(self.event_src),
				'msg': {
					'type': self.msg['type'],
					'ir': json_util.dumps(self.msg['ir']),
					'state': self.msg['state']
				}
			})
		elif self.msg['type'] == TE_EVENT_TYPE.IR_ADD:
			return json.dumps({
				'event_src': str(self.event_src),
				'msg': {
					'type': self.msg['type'],
					'ir': json_util.dumps(self.msg['ir']),
					'sw': self.msg['sw']
				}
			})
		elif self.msg['type'] == TE_EVENT_TYPE.IR_REM:
			return json.dumps({
				'event_src': str(self.event_src),
				'msg': {
					'type': self.msg['type'],
					'ir': json_util.dumps(self.msg['ir'])
				}
			})
		elif self.msg['type'] == TE_EVENT_TYPE.TOPO_MOD:
			return json.dumps({
				'event_src': str(self.event_src),
				'msg': {
					'type': self.msg['type'],
					'sw': self.msg['sw'],
					'state': self.msg['state']
				}
			})
		elif self.msg['type'] == TE_EVENT_TYPE.FO_RESET:
			return json.dumps({
				'event_src': str(self.event_src),
				'msg': {
					'type': self.msg['type']
				}
			})
		return json.dumps({
			'event_src': str(self.event_src),
			'msg': {
				'type': self.msg['type'],
				'sw': self.msg['sw']
			}
		})

	@staticmethod
	def deserialize(msg_bytes):
		res = json.loads(msg_bytes)
		if res['msg']['type'] in {TE_EVENT_TYPE.IR_MOD, TE_EVENT_TYPE.IR_ADD}:
			res['msg']['ir'] = json_util.loads(res['msg']['ir'])

		return TEEvent(
			event_src=res['event_src'],
			msg=res['msg']
		)


class DAGEvent(NIBEventBase):
	def __init__(self, *args, **kwargs):
		super(DAGEvent, self).__init__(*args, **kwargs)

	def __str__(self):
		if self.msg['type'] == DAG_EVENT_TYPE.DAG_STALE:
			return f"Stale DAG for {short_uid(self.msg['id'])}"
		elif self.msg['type'] == DAG_EVENT_TYPE.DAG_NEW:
			return f"New DAG for {short_uid(self.msg['obj'].uid)}"
		return super(DAGEvent, self).__str__()

	def __eq__(self, other):
		if isinstance(other, DAGEvent):
			if not other.msg['type'] == self.msg['type']:
				return False
			if other.msg['type'] == DAG_EVENT_TYPE.DAG_STALE:
				return other.msg['id'] == self.msg['id']
			if other.msg['type'] == DAG_EVENT_TYPE.DAG_NEW:
				return other.msg['obj'].uid == self.msg['obj'].uid
		return False


class IRScheduleEvent:
	def __init__(self, ir, tag):
		self.ir = ir
		self.tag = tag

	def __str__(self):
		return f"IR = {self.ir} | tag = {self.tag}"

	def serialize(self):
		return json.dumps({
			'ir': self.ir.get_json_dict(),
			'tag': self.tag
		})

	@staticmethod
	def deserialize(msg_bytes):
		res = json.loads(msg_bytes)
		return IRScheduleEvent(
			ir=IR.parse_from_json_dict(res['ir']),
			tag=res['tag']
		)


class DAGScheduleEvent(NIBEventBase):
	def __init__(self, *args, **kwargs):
		super(DAGScheduleEvent, self).__init__(*args, **kwargs)

	def __str__(self):
		return "DAGScheduleEvent " + super(DAGScheduleEvent, self).__str__()


class QueuedIR:
	# def __init__(self, ir: IR, item_id, tag):
	def __init__(self, ir: IR, tag):
		self.ir = ir
		# self.item_id = item_id
		self.tag = tag

	@classmethod
	def parse_from_nib(cls, nib_res: Dict):
		if not nib_res:
			return None

		return cls(
			ir=IR.parse_from_nib(nib_res['ir']),
			# item_id=nib_res['_id'],
			tag=nib_res['tag']
		)

	@classmethod
	def parse_from_json_dict(cls, json_dict):
		# return cls(IR.parse_from_json_dict(json_dict['ir']), json_util.loads(json_dict['item_id']), json_dict['tag'])
		return cls(IR.parse_from_json_dict(json_dict['ir']), json_dict['tag'])

	def __str__(self):
		# return f"Queue item {short_uid(self.item_id)}: {self.ir.type} on {self.ir.dp_id} | UID: {short_uid(self.ir.uid)}"
		return f"Queue item {self.ir.type} on {self.ir.dp_id} | UID: {short_uid(self.ir.uid)}"

	def _get_json_dict(self):
		return {
			'ir': self.ir.get_json_dict(),
			# 'item_id': json_util.dumps(self.item_id),
			'tag': self.tag
		}

	def serialize(self):
		return json.dumps({
			'ir': self.ir.get_json_dict(),
			'tag': self.tag
		})

	@staticmethod
	def deserialize(msg_bytes):
		res = json.loads(msg_bytes)
		return QueuedIR(
			ir=IR.parse_from_json_dict(res['ir']),
			tag=res['tag']
		)
