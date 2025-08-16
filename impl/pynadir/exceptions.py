import ctypes

class NadirLazyAccessDomainError(Exception):
    """
    This means that both the following happened:
        - The key did not exist in the mapping for this function
        - No initial values were set for this function
    """
    pass

class GreedyAccessDomainError(Exception):
    """
    This happens when a function access has no value mapped to a particular
    domain value.
    """
    pass

class ExecutionHalted(Exception):
    """
    The execution was interrupted with a signal, time to 
    fully exit.
    """
    pass

class RepeatLabel(Exception):
    """
    The execution of this label was aborted, it must be
    re-evaluated.
    """
    pass

class UnsupportedType(Exception):
    """
    A Nadir provider encountered a value that it has no idea
    how to handle.
    """
    pass

class WaitThenRepeat(Exception):
    """
    Wait for some time, then repeat the label.
    """

    def __init__(self, wait_for: float, *args: object) -> None:
        super().__init__(*args)
        self.wait_for = wait_for


def explode():
    """
    This is useful for simulating stopping failures.
    Will cause the interpreter SEGFAULT, killing the process with it.
    """
    print("BOOOOM!")
    p = ctypes.pointer(ctypes.c_char.from_address(1))
    return p[1]
