"""
Some basic exceptions for OpenFlow
"""


class OpenFlowException(Exception):
	def __init__(self, msg="Unknown OpenFlow error"):
		super(OpenFlowException, self).__init__(msg)


class VersionNotSupported(OpenFlowException):
	def __init__(self, bad_version):
		super(VersionNotSupported, self).__init__(f"Version {bad_version} is not supported")


class MalformedMessage(OpenFlowException):
	def __init__(self, bad_version):
		super(MalformedMessage, self).__init__("Malformed message")


class TruncatedMessage(OpenFlowException):
	def __init__(self, msg):
		super(TruncatedMessage, self).__init__(f"Truncated message: {msg}")


class InvalidActionString(OpenFlowException):
	def __init__(self, action_str):
		super(InvalidActionString, self).__init__(f"Cannot parse action string {action_str}")
