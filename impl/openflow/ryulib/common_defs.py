"""
Holds common definitions for 1.3
"""

from struct import calcsize


OFP_HEADER_PACK_STR = "!BBHI"
OFP_HEADER_SIZE = 8
assert calcsize(OFP_HEADER_PACK_STR) == OFP_HEADER_SIZE

OFP_TCP_PORT = 6653
OFP_TCP_PORT_OLD = 6633
MAX_XID = 0xffffffff
