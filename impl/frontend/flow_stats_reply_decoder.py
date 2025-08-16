import openflow.ryulib.openflow_v13_parser as parser


class FlowStatReplyDecoder:
	# This is as simple as it gets!!!!
	
	@classmethod
	def get_cookies(cls, reply: parser.OFPFlowStatsReply):
		return set([stats.cookie for stats in reply.body])

