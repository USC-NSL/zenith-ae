import time
import queue
import openflow.ryulib.openflow_v13_parser as maker
import openflow.ryulib.openflow_v13_defs as defs
from openflow.zenith_defs import OpenFlowEvent
from openflow.ofc_defs import SwitchStatusChangeEvent, SWITCH_TO_CONTROLLER_TYPES
from frontend.frontend_defs import MSEvent
from frontend.flow_stats_reply_decoder import FlowStatReplyDecoder


class OpenFlowEventHandlers:
	MAX_NUMBER_OF_EVENTS = 256
	HANDLER_QUEUE = queue.Queue(MAX_NUMBER_OF_EVENTS)
	stop = False
	
	datapath_on_connection_method = None
	ms_queue = None
	sw_change_queue =  None

	@classmethod
	def set_datapath_on_connection_method(cls, method):
		cls.datapath_on_connection_method = method

	@classmethod
	def set_ms_queue(cls, ms_queue):
		cls.ms_queue = ms_queue

	@classmethod
	def set_sw_change_queue(cls, queue):
		cls.sw_change_queue = queue

	@classmethod
	def handler_is_ready(cls):
		return (cls.datapath_on_connection_method is not None) and \
			(cls.ms_queue is not None) and \
			(cls.sw_change_queue is not None) 

	@classmethod
	def put_event(cls, event: OpenFlowEvent):
		cls.HANDLER_QUEUE.put(event)

	@classmethod
	def put_sw_change_event(cls, dp_id, reason):
		cls.sw_change_queue.put(SwitchStatusChangeEvent(dp_id, reason))

	@classmethod
	def get_event(cls) -> OpenFlowEvent:
		event = cls.HANDLER_QUEUE.get()
		return event

	@classmethod
	def finish(cls):
		cls.stop = True

	@classmethod
	def generic_handler(cls):
		while not cls.stop:
			event = cls.get_event()
			if cls.stop:
				break
			openflow_message = event.openflow_message

			handler = _ROUTER.get(openflow_message.__class__)
			if handler:
				handler(event) # noqa

	@classmethod
	def _hello_failed(cls, datapath, reported_version):
		error_desc = f'unsupported version {reported_version}. Set to 1.3!'
		error_msg = maker.OFPErrorMsg(
			datapath=datapath, type=defs.OFPET_HELLO_FAILED,
			code=defs.OFPHFC_INCOMPATIBLE, data=error_desc
		)
		datapath.send_msg(error_msg, close_socket=True)

	@classmethod
	def hello_handler(cls, event: OpenFlowEvent):
		openflow_message = event.openflow_message
		datapath = event.datapath
		assert isinstance(openflow_message, maker.OFPHello)
		version = openflow_message.elements[0].versions[0]
		if version == 0x04:
			# send features request
			features_request = maker.OFPFeaturesRequest(datapath)
			datapath.send_msg(features_request)
		else:
			cls._hello_failed(datapath, version)

	@classmethod
	def echo_reply_handler(cls, event: OpenFlowEvent):
		event.datapath.acknowledge_echo_reply(event.openflow_message.xid)

	@classmethod
	def features_reply_handler(cls, event: OpenFlowEvent):
		openflow_message = event.openflow_message
		datapath = event.datapath

		datapath.dp_id = openflow_message.datapath_id
		cls.datapath_on_connection_method(datapath.dp_id, datapath)

		port_desc = maker.OFPPortDescStatsRequest(datapath, 0)
		datapath.send_msg(port_desc)

	@classmethod
	def echo_request_handler(cls, event: OpenFlowEvent):
		openflow_message = event.openflow_message
		datapath = event.datapath
		echo_reply = maker.OFPEchoReply(datapath)
		echo_reply.xid = openflow_message.xid
		echo_reply.data = openflow_message.data
		datapath.send_msg(echo_reply)

	@classmethod
	def flow_stats_reply_handler(cls, event: OpenFlowEvent):
		openflow_message = event.openflow_message
		datapath = event.datapath
		cookies = FlowStatReplyDecoder.get_cookies(openflow_message)
		cls.ms_queue.put(MSEvent(
			type=SWITCH_TO_CONTROLLER_TYPES.FLOW_STAT_REPLY,
			dp_id=datapath.dp_id,
			msg={
				'cookies': cookies
			}
		))

	@classmethod
	def barrier_reply_handler(cls, event: OpenFlowEvent):
		openflow_message = event.openflow_message
		datapath = event.datapath
		
		cookie = datapath.barrier_map.pop(openflow_message.xid, None)
		if cookie is not None:
			cls.ms_queue.put(MSEvent(
				type=SWITCH_TO_CONTROLLER_TYPES.INSTALLED_SUCCESSFULLY,
				dp_id=datapath.dp_id,
				msg={
					'cookie': cookie
				}
			))
			return

		cookie = datapath.flow_rem_map.pop(openflow_message.xid, None)
		if cookie is not None:
			if cookie == 0:
				cls.ms_queue.put(MSEvent(
					type=SWITCH_TO_CONTROLLER_TYPES.CLEARED_TCAM_SUCCESSFULLY,
					dp_id=datapath.dp_id,
					msg={
						'timestamp': int(time.time())
					}
				))
			else:
				cls.ms_queue.put(MSEvent(
					type=SWITCH_TO_CONTROLLER_TYPES.DELETED_SUCCESSFULLY,
					dp_id=datapath.dp_id,
					msg={
						'cookie': cookie
					}
				))
			return

	@classmethod
	def error_handler(cls, event: OpenFlowEvent):
		openflow_message = event.openflow_message
		datapath = event.datapath

		error_type = openflow_message.type
		error_code = openflow_message.code

		raise RuntimeError(f"Got error on DP {datapath}: {error_type}: {error_code}")


_ROUTER = {
	maker.OFPHello: OpenFlowEventHandlers.hello_handler,
	maker.OFPEchoRequest: OpenFlowEventHandlers.echo_request_handler,
	maker.OFPEchoReply: OpenFlowEventHandlers.echo_reply_handler,
	maker.OFPSwitchFeatures: OpenFlowEventHandlers.features_reply_handler,
	maker.OFPBarrierReply: OpenFlowEventHandlers.barrier_reply_handler,
	maker.OFPFlowStatsReply: OpenFlowEventHandlers.flow_stats_reply_handler,
	maker.OFPErrorMsg: OpenFlowEventHandlers.error_handler
}