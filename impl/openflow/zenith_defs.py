import time


class OpenFlowEvent:
	def __init__(self, datapath, openflow_message):
		self.datapath = datapath
		self.timestamp = time.time()
		self.openflow_message = openflow_message


class MSEvent:
	def __init__(self, type, dp_id, msg):
		self.type = type
		self.dp_id = dp_id
		self.msg = msg
		self.timestamp = time.time()
