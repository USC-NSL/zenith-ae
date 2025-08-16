import six
from openflow.ryulib.utils import l2


# string representation
HADDR_PATTERN = r'([0-9a-f]{2}:){5}[0-9a-f]{2}'

DONTCARE = b'\x00' * 6
BROADCAST = b'\xff' * 6
DONTCARE_STR = '00:00:00:00:00:00'
BROADCAST_STR = 'ff:ff:ff:ff:ff:ff'
MULTICAST = 'fe:ff:ff:ff:ff:ff'
UNICAST = '01:00:00:00:00:00'


def is_multicast(addr):
    return bool(int(addr[0]) & 0x01)


def haddr_to_str(addr):
    """Format mac address in internal representation into human readable
    form"""
    if addr is None:
        return 'None'
    try:
        return l2.bin_to_text(addr)
    except:
        raise AssertionError


def haddr_to_int(addr):
    """Convert mac address string in human readable format into
    integer value"""
    try:
        return int(addr.replace(':', ''), 16)
    except:
        raise ValueError


def haddr_to_bin(string):
    """Parse mac address string in human readable format into
    internal representation"""
    try:
        return l2.text_to_bin(string)
    except:
        raise ValueError


def haddr_bitand(addr, mask):
    return b''.join(six.int2byte(int(a) & int(m)) for (a, m)
                    in zip(addr, mask))
