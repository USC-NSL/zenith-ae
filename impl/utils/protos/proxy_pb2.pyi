from google.protobuf import empty_pb2 as _empty_pb2
from google.protobuf.internal import containers as _containers
from google.protobuf import descriptor as _descriptor
from google.protobuf import message as _message
from typing import ClassVar as _ClassVar, Iterable as _Iterable, Mapping as _Mapping, Optional as _Optional, Union as _Union

DESCRIPTOR: _descriptor.FileDescriptor

class DPIDMessage(_message.Message):
    __slots__ = ("dp_id",)
    DP_ID_FIELD_NUMBER: _ClassVar[int]
    dp_id: int
    def __init__(self, dp_id: _Optional[int] = ...) -> None: ...

class QueryDatapathResponse(_message.Message):
    __slots__ = ("cookies",)
    COOKIES_FIELD_NUMBER: _ClassVar[int]
    cookies: _containers.RepeatedScalarFieldContainer[int]
    def __init__(self, cookies: _Optional[_Iterable[int]] = ...) -> None: ...

class QueryAllResponse(_message.Message):
    __slots__ = ("tcams",)
    class TcamsEntry(_message.Message):
        __slots__ = ("key", "value")
        KEY_FIELD_NUMBER: _ClassVar[int]
        VALUE_FIELD_NUMBER: _ClassVar[int]
        key: int
        value: QueryDatapathResponse
        def __init__(self, key: _Optional[int] = ..., value: _Optional[_Union[QueryDatapathResponse, _Mapping]] = ...) -> None: ...
    TCAMS_FIELD_NUMBER: _ClassVar[int]
    tcams: _containers.MessageMap[int, QueryDatapathResponse]
    def __init__(self, tcams: _Optional[_Mapping[int, QueryDatapathResponse]] = ...) -> None: ...
