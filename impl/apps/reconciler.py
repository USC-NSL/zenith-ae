import time
import random
from collections import deque
from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros
from pynadir.utils.logging import TitledLog # NO_GEN


class controllerReconciliationScheduler(NadirProcess):
    num_cvs = 0

    def ControllerReconciler(self, local_provider):
        if local_provider.get_value("inflight", self.get_pid()) == 1:
            local_provider.set_value(self.get_pid(), "inflight", 0)
        local_provider.set_value(self.get_pid(), "coeff", 1)
        return "WaitUntilReconciliationEvent"

    def WaitUntilReconciliationEvent(self, local_provider):
        T = local_provider.get_value("RECONCILIATION_PERIOD", self.get_pid())
        coeff = local_provider.get_value("coeff", self.get_pid())
        time.sleep(T * coeff)
        if not self.global_provider.get_value("seqWorkerIsBusy", self.get_pid()):
            TitledLog.info("pr", "Sequencer is not busy. Scheduling reconciliation request") # NO_GEN
            local_provider.set_value(self.get_pid(), "switches", deque(self.input_provider.get_value("SW", self.get_pid())))
            return "SendDirectedReconciliationRequest"

        if self.global_provider.looks_empty(self.get_pid(), "IRQueueNIB"): # noqa
            TitledLog.warning("pr", "Sequencer is busy, but the IR queue is empty! Scheduling reconciliation request") # NO_GEN
            local_provider.set_value(self.get_pid(), "switches", deque(self.input_provider.get_value("SW", self.get_pid())))
            return "SendDirectedReconciliationRequest"

        local_provider.set_value(self.get_pid(), "coeff", random.random())
        TitledLog.info("pr", "A DAG is being actively processed. Will postpone reconciliation") # NO_GEN
        return "WaitUntilReconciliationEvent"

    def SendDirectedReconciliationRequest(self, local_provider):
        switches = local_provider.get_value("switches", self.get_pid())
        if len(switches) > 0:
            switch = switches.popleft()
            macros.controllerSendDirectedReconciliation(self, local_provider, switch)
            local_provider.set_value(self.get_pid(), "inflight", 1)
        else:
            return "ControllerReconciler"
        return "SendDirectedReconciliationRequest"
