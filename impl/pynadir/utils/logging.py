import time
import multiprocessing
from typing import Optional


class ANSIColors:
    GRAY = '\033[90m'
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WHITE = '\033[97m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


as_bold = lambda msg: f"{ANSIColors.BOLD}{msg}{ANSIColors.ENDC}"
as_warning = lambda msg: f"{ANSIColors.BOLD}{ANSIColors.WARNING}{msg}{ANSIColors.ENDC}"
as_trace = lambda msg: f"{ANSIColors.GRAY}{msg}{ANSIColors.ENDC}"
as_debug = lambda msg: f"{ANSIColors.WHITE}{msg}{ANSIColors.ENDC}"
as_info = lambda msg: f"{ANSIColors.OKBLUE}{msg}{ANSIColors.ENDC}"
as_special_info = lambda msg: f"{ANSIColors.BOLD}{ANSIColors.OKCYAN}{msg}{ANSIColors.ENDC}"
as_success = lambda msg: f"{ANSIColors.BOLD}{ANSIColors.OKGREEN}{msg}{ANSIColors.ENDC}"
as_fail = lambda msg: f"{ANSIColors.BOLD}{ANSIColors.FAIL}{msg}{ANSIColors.ENDC}"


class TitledLog:
    TITLE_LEN = 10
    TIMESTAMP_LEN = 8
    
    _QUEUE: Optional[multiprocessing.Queue] = None
    _START_TIME: Optional[int] = None
    _LEVEL = 0

    @classmethod
    def set_start_time(cls, value: Optional[int] = None):
        assert cls._START_TIME is None
        if value:
            cls._START_TIME = value
        else:
            cls._START_TIME = time.perf_counter_ns()
    
    @classmethod
    def get_start_time(cls) -> Optional[int]:
        return cls._START_TIME
    
    @classmethod
    def set_out_queue(cls, value: Optional[multiprocessing.Queue]):
        assert cls._QUEUE is None
        cls._QUEUE = value

    @classmethod
    def get_out_queue(cls) -> Optional[multiprocessing.Queue]:
        return cls._QUEUE

    @classmethod
    def get_timestamp(cls) -> Optional[str]:
        if cls._START_TIME is not None:
            return str(round((time.perf_counter_ns() - cls._START_TIME)/1e9, 3))
        return None
    
    @classmethod
    def set_log_level(cls, value: int):
        cls._LEVEL = value

    @classmethod
    def create_title(cls, title: str, padding: Optional[int] = None, 
                     with_timestamp: bool = True, upper: bool = True):
        padding = padding if padding is not None else cls.TITLE_LEN
        title = title if not upper else title.upper()
        if with_timestamp:
            timestamp = cls.get_timestamp()
            if timestamp:
                return "[{:^{padding}}][{:^{time_padding}}]".format(
                    title, timestamp,
                    padding=padding, 
                    time_padding=cls.TIMESTAMP_LEN)
        return "[{:^{padding}}]".format(title, padding=padding)

    @classmethod
    def titled_message(cls, title: str, message: str):
        return f"{cls.create_title(title)} {message}"
    
    @classmethod
    def emit_message(cls, msg: str, both: bool = False):
        if both or cls.get_out_queue() is None:
            print(msg)
        if cls.get_out_queue() is not None:
            try:
                cls.get_out_queue().put(msg)
            except ValueError:
                # If the queue gets closed because the other process died ...
                pass
    @classmethod
    def trace(cls, title: str, msg: str, both: bool = False):
        if cls._LEVEL > 0:
            return
        cls.emit_message(as_trace(cls.titled_message(title, msg)), both=both)
    @classmethod
    def debug(cls, title: str, msg: str, both: bool = False):
        if cls._LEVEL > 1:
            return
        cls.emit_message(as_debug(cls.titled_message(title, msg)), both=both)
    @classmethod
    def info(cls, title: str, msg: str, both: bool = False):
        if cls._LEVEL > 2:
            return
        cls.emit_message(as_info(cls.titled_message(title, msg)), both=both)
    @classmethod
    def special_info(cls, title: str, msg: str, both: bool = False):
        if cls._LEVEL > 3:
            return
        cls.emit_message(as_special_info(cls.titled_message(title, msg)), both=both)
    @classmethod
    def warning(cls, title: str, msg: str, both: bool = False):
        if cls._LEVEL > 3:
            return
        cls.emit_message(as_warning(cls.titled_message(title, msg)), both=both)
    @classmethod
    def fail(cls, title: str, msg: str, both: bool = False):
        cls.emit_message(as_fail(cls.titled_message(title, msg)), both=both)
    @classmethod
    def success(cls, title: str, msg: str, both: bool = False):
        cls.emit_message(as_success(cls.titled_message(title, msg)), both=both)
