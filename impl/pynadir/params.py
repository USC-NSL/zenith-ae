from threading import Event


"""
All global params go to the class below for now. Let's keep it
simple until we _have_ to change it.
"""

class _NadirParams:
    def __init__(self, build_id: str) -> None:
        self.build_id = build_id
        self.is_active = True
        self.quit_event = Event()

    def stop(self):
        self.is_active = False
        self.quit_event.set()


NadirGlobalParams = _NadirParams("aragif")
