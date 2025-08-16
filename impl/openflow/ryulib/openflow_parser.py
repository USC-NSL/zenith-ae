import struct
import functools
import openflow.ryulib.utils as utils
import openflow.ryulib.openflow_exceptions as openflow_exceptions
from openflow.ryulib.common_defs import OFP_HEADER_PACK_STR
from openflow.ryulib.openflow_v13_defs import OFP_VERSION
from openflow.ryulib.openflow_v13_parser import msg_parser, OFPHello


def unpack_header(buf):
    return struct.unpack_from(OFP_HEADER_PACK_STR, buf)

def get_hello(datapath):
    return OFPHello(datapath)

"""
This invokes a generic method for parsing a given message.
It is much more simple for us since we only implement 1.3
"""
def msg(datapath, version, msg_type, msg_len, xid, buf):
    exp = None
    try:
        assert len(buf) >= msg_len
    except AssertionError as e:
        exp = e

    if version != OFP_VERSION:
        raise openflow_exceptions.VersionNotSupported(version)

    try:
        msg = msg_parser(datapath, version, msg_type, msg_len, xid, buf)
    except openflow_exceptions.TruncatedMessage(buf) as e:
        raise e
    except:
        print(
            'Encountered an error while parsing OpenFlow packet from switch. '
            'This implies the switch sent a malformed OpenFlow packet. '
            'version 0x%02x msg_type %d msg_len %d xid %d buf %s',
            version, msg_type, msg_len, xid, utils.hex_array(buf))
        msg = None
    if exp:
        raise exp
    return msg


def create_list_of_base_attributes(f):
    @functools.wraps(f)
    def wrapper(self, *args, **kwargs):
        ret = f(self, *args, **kwargs)
        cls = self.__class__
        # hasattr(cls, '_base_attributes') doesn't work because super class
        # may already have the attribute.
        if '_base_attributes' not in cls.__dict__:
            cls._base_attributes = set(dir(self))
        return ret
    return wrapper
