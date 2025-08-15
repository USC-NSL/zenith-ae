------------------- MODULE switch -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, NadirTypes

(*--fair algorithm switch
    variables 
        switchLock = <<NO_LOCK, NO_LOCK>>,
        controllerLock = <<NO_LOCK, NO_LOCK>>,
        sw_fail_ordering_var = SW_FAIL_ORDERING,
        
        controller2Switch = [x \in SW |-> <<>>],
        switch2Controller = <<>>, 
        switchStatus = [
            x \in SW |-> [
                cpu |-> NotFailed, 
                nicAsic |-> NotFailed, 
                ofa |-> NotFailed, 
                installer |-> NotFailed
            ]
        ],  
        installedIRs = <<>>,

        NicAsic2OfaBuff = [x \in SW |-> <<>>], 
        Ofa2NicAsicBuff = [x \in SW |-> <<>>],
        Installer2OfaBuff = [x \in SW |-> <<>>],
        Ofa2InstallerBuff = [x \in SW |-> <<>>],

        TCAM = [x \in SW |-> {}], 

        controlMsgCounter = [x \in SW |-> 0],
        RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
    
    define
        removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                                    ELSE inSeq[j+1]]
        
        swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed 
        swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                                  /\ switchStatus[sw].ofa = NotFailed
        
        existMatchingEntryTCAM(swID, flowID) == flowID \in TCAM[swID]
        swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                               /\ switchStatus[sw].cpu = NotFailed
        
        returnSwitchElementsNotFailed(sw) == {
            x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                           /\ \/ /\ WHICH_SWITCH_MODEL[x] = SW_COMPLEX_MODEL
                                                 /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1
                                              \/ /\ WHICH_SWITCH_MODEL[x] = SW_SIMPLE_MODEL
                                                 /\ x = "nicAsic"
        }
        returnSwitchFailedElements(sw) == {
            x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                           /\ \/ switchStatus[sw].cpu = NotFailed
                                              \/ x \notin {"ofa", "installer"}
        }
        installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerProc" 
        ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaProcIn"
                                 /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaProcOut"
        nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchRcvPacket"
                                     /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchFromOFAPacket"
        getInstallerStatus(stat) == IF stat = NotFailed 
                                    THEN INSTALLER_UP
                                    ELSE INSTALLER_DOWN     
    end define
    
    (*******************************************************************)
    (*                       Utils (Macros)                            *)
    (*******************************************************************)
    macro removeFromSeqSet(SeqSet, obj)
    begin
        assert obj \in Head(SeqSet);
        if Cardinality(Head(SeqSet)) = 1 then
            SeqSet := Tail(SeqSet);
        else
            SeqSet := <<(Head(SeqSet)\{obj})>> \o Tail(SeqSet);
        end if; 
    end macro
    
    (*******************************************************************)
    (*                     Switches (Macros)                           *)
    (*******************************************************************)
    macro completeFailure()
    begin
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusMsg := [type |-> NIC_ASIC_DOWN, 
                            swID |-> self[2],
                            num |-> controlMsgCounter[self[2]]];
            switch2Controller := Append(switch2Controller, statusMsg);
        end if;
        
        switchStatus[self[2]] := [cpu |-> Failed, nicAsic |-> Failed, 
                                    ofa |-> Failed, installer |-> Failed];
        NicAsic2OfaBuff[self[2]] := <<>>; 
        Ofa2NicAsicBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        TCAM[self[2]] := {};
        controller2Switch[self[2]] := <<>>;    
    end macro;

    macro resolveCompleteFailure()
    begin
        assert switchStatus[self[2]].cpu = Failed;
        assert switchStatus[self[2]].nicAsic = Failed;
        assert switchStatus[self[2]].ofa = Failed;
        assert switchStatus[self[2]].installer = Failed;
        
        await nicAsicStartingMode(self[2]);
        await ofaStartingMode(self[2]);
        await installerInStartingMode(self[2]);
        
        switchStatus[self[2]] := [cpu |-> NotFailed, nicAsic |-> NotFailed, 
                                    ofa |-> NotFailed, installer |-> NotFailed];
        NicAsic2OfaBuff[self[2]] := <<>>; 
        Ofa2NicAsicBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        TCAM[self[2]] := {};
        controller2Switch[self[2]] := <<>>;
        
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
        statusResolveMsg := [
            type |-> KEEP_ALIVE, 
            swID |-> self[2],
            num |-> controlMsgCounter[self[2]],
            installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
        ];  
        switch2Controller := Append(switch2Controller, statusResolveMsg);  
    end macro;

    macro nicAsicFailure()
    begin
        assert switchStatus[self[2]].nicAsic = NotFailed;
        switchStatus[self[2]].nicAsic := Failed;
        controller2Switch[self[2]] := <<>>;
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
        statusMsg := [
            type |-> NIC_ASIC_DOWN, 
            swID |-> self[2],
            num |-> controlMsgCounter[self[2]]
        ];
        switch2Controller := Append(switch2Controller, statusMsg);              
    end macro

    macro resolveNicAsicFailure()
    begin
        await nicAsicStartingMode(self[2]);
        assert switchStatus[self[2]].nicAsic = Failed;
        switchStatus[self[2]].nicAsic := NotFailed;
        controller2Switch[self[2]] := <<>>;  
        if switchStatus[self[2]].ofa = Failed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusResolveMsg := [
                type |-> OFA_DOWN, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]]
            ];
        else
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusResolveMsg := [
                type |-> KEEP_ALIVE, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ];
        end if;
        switch2Controller := Append(switch2Controller, statusResolveMsg);            
    end macro

    macro cpuFailure()
    begin
        assert switchStatus[self[2]].cpu = NotFailed;
        switchStatus[self[2]].cpu := Failed || switchStatus[self[2]].ofa := Failed || switchStatus[self[2]].installer := Failed;
        NicAsic2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2NicAsicBuff[self[2]] := <<>>;
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
            statusMsg := [
                type |-> OFA_DOWN, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]]
            ];
            switch2Controller := Append(switch2Controller, statusMsg);
        end if;
    end macro

    macro resolveCpuFailure()
    begin
        await ofaStartingMode(self[2]) /\ installerInStartingMode(self[2]);
        assert switchStatus[self[2]].cpu = Failed;
        switchStatus[self[2]].cpu := NotFailed || switchStatus[self[2]].ofa := NotFailed || switchStatus[self[2]].installer := NotFailed;
        NicAsic2OfaBuff[self[2]] := <<>>;
        Ofa2InstallerBuff[self[2]] := <<>>;
        Installer2OfaBuff[self[2]] := <<>>;
        Ofa2NicAsicBuff[self[2]] := <<>>;       
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusResolveMsg := [
                type |-> KEEP_ALIVE, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ]; 
            switch2Controller := Append(switch2Controller, statusResolveMsg);    
        end if;
    end macro

    macro ofaFailure()
    begin
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed;
        switchStatus[self[2]].ofa := Failed;       
        if switchStatus[self[2]].nicAsic = NotFailed then  
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;  
            statusMsg := [
                type |-> OFA_DOWN, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]]
            ];
            switch2Controller := Append(switch2Controller, statusMsg);    
        end if;
    end macro

    macro resolveOfaFailure()
    begin
        await ofaStartingMode(self[2]);
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = Failed;
        switchStatus[self[2]].ofa := NotFailed;          
        if switchStatus[self[2]].nicAsic = NotFailed then
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;   
            statusResolveMsg := [
                type |-> KEEP_ALIVE, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ];
            switch2Controller := Append(switch2Controller, statusResolveMsg);             
        end if;
    end macro

    macro installerFailure()
    begin
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed;
        switchStatus[self[2]].installer := Failed;  
        if switchStatus[self[2]].nicAsic = NotFailed /\ switchStatus[self[2]].ofa = NotFailed then
            assert switchStatus[self[2]].installer = Failed;
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusMsg := [
                type |-> KEEP_ALIVE, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ];
            switch2Controller := Append(switch2Controller, statusMsg);
        end if;
    end macro

    macro resolveInstallerFailure()
    begin
        await installerInStartingMode(self[2]);
        assert switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = Failed;
        switchStatus[self[2]].installer := NotFailed;         
        if switchStatus[self[2]].nicAsic = NotFailed /\ switchStatus[self[2]].ofa = NotFailed then
            assert switchStatus[self[2]].installer = NotFailed;
            controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;    
            statusResolveMsg := [
                type |-> KEEP_ALIVE, 
                swID |-> self[2],
                num |-> controlMsgCounter[self[2]],
                installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
            ];
            switch2Controller := Append(switch2Controller, statusResolveMsg);    
        end if;
    end macro

    macro installToTCAM(newFlow)
    begin
        installedIRs := Append(installedIRs, newFlow);
        TCAM[self[2]] := TCAM[self[2]] \cup {newFlow};
    end macro

    macro removeFromTCAM(flowID)
    begin
        TCAM[self[2]] := (TCAM[self[2]] \ {flowID});
    end macro

    macro clearTCAM() begin
        TCAM[self[2]] := {};
    end macro;

    macro switchSend(msg)
    begin
        if WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL then
            switch2Controller := Append(switch2Controller, msg);
        else
            Ofa2NicAsicBuff[self[2]] := Append(Ofa2NicAsicBuff[self[2]], msg);
        end if;
    end macro

    macro sendConfirmation(controllerID, flowID, statusType)
    begin
        switchSend([
            type |-> statusType, 
            from |-> self[2], 
            to |-> controllerID,
            flow |-> flowID
        ]);
    end macro

    macro sendClearConfirmation() begin
        controlMsgCounter[self[2]] := controlMsgCounter[self[2]] + 1;
        if WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL then
            switch2Controller := Append(
                switch2Controller, 
                [
                    type |-> CLEARED_TCAM_SUCCESSFULLY, 
                    swID |-> self[2],
                    num |-> controlMsgCounter[self[2]],
                    installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                ]
            );
        else
            Ofa2NicAsicBuff[self[2]] := Append(
                Ofa2NicAsicBuff[self[2]], 
                [
                    type |-> CLEARED_TCAM_SUCCESSFULLY, 
                    swID |-> self[2],
                    num |-> controlMsgCounter[self[2]],
                    installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                ]
            );
        end if;
    end macro;
    
    (*******************************************************************)
    (*                     LOCK System (Macros)                        *)
    (*******************************************************************)

    macro switchWaitForLock()
    begin     
        await controllerLock = <<NO_LOCK, NO_LOCK>>; 
        await switchLock \in {<<NO_LOCK, NO_LOCK>>, self};
    end macro;

    macro switchAcquireLock()
    begin
        switchWaitForLock();
        switchLock := self;
    end macro;

    macro acquireAndChangeLock(nextLockHolder)
    begin
        switchWaitForLock();
        switchLock := nextLockHolder;
    end macro;

    macro releaseLock(prevLockHolder)
    begin
        assert \/ switchLock[2] = prevLockHolder[2]
               \/ switchLock[2] = NO_LOCK;
        switchLock := <<NO_LOCK, NO_LOCK>>;
    end macro;
        
    (*******************************************************************)
    (*                     Switches SIMPLE Model                       *)
    (*******************************************************************)

    fair process swProcess \in ({SW_SIMPLE_ID} \X SW)
    variables ingressPkt = NADIR_NULL
    begin
    SwitchSimpleProcess:
    while TRUE do
        await whichSwitchModel(self[2]) = SW_SIMPLE_MODEL; 
        await swCanReceivePackets(self[2]);         
        await Len(controller2Switch[self[2]]) > 0;
        switchWaitForLock();
        ingressPkt := Head(controller2Switch[self[2]]);
        assert ingressPkt.type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM};
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);
        if ingressPkt.type = INSTALL_FLOW then
            installToTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, INSTALLED_SUCCESSFULLY);
        elsif ingressPkt.type = DELETE_FLOW then
            removeFromTCAM(ingressPkt.flow);
            sendConfirmation(ingressPkt.from, ingressPkt.flow, DELETED_SUCCESSFULLY);
        elsif ingressPkt.type = CLEAR_TCAM then
            clearTCAM();
            sendClearConfirmation();
        end if;
        releaseLock(self);
    end while;
    end process;
    
    (*******************************************************************)
    (*                     Switches COMPLEX (Modules)                  *)
    (*******************************************************************)
    
    fair process swNicAsicProcPacketIn \in ({NIC_ASIC_IN} \X SW)
    variables ingressIR = NADIR_NULL
    begin
    SwitchRcvPacket:
    while TRUE do
        await whichSwitchModel(self[2]) = SW_COMPLEX_MODEL;
        await swCanReceivePackets(self[2]);
        await Len(controller2Switch[self[2]]) > 0;
        ingressIR := Head(controller2Switch[self[2]]);
        assert ingressIR.type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM};
        switchAcquireLock();
        controller2Switch[self[2]] := Tail(controller2Switch[self[2]]);

        SwitchNicAsicInsertToOfaBuff:
            if swCanReceivePackets(self[2]) then
                acquireAndChangeLock(<<OFA_IN, self[2]>>);
                NicAsic2OfaBuff[self[2]] := Append(NicAsic2OfaBuff[self[2]], ingressIR); 
            else
                goto SwitchRcvPacket;
            end if;
    end while;
    end process
    
    fair process swNicAsicProcPacketOut \in ({NIC_ASIC_OUT} \X SW)
    variables egressMsg = NADIR_NULL
    begin
    SwitchFromOFAPacket:
    while TRUE do
        await swCanReceivePackets(self[2]);
        await  Len(Ofa2NicAsicBuff[self[2]]) > 0;
        egressMsg := Head(Ofa2NicAsicBuff[self[2]]);
        switchAcquireLock();
        assert egressMsg.type \in {INSTALLED_SUCCESSFULLY, 
                                   DELETED_SUCCESSFULLY,
                                   CLEARED_TCAM_SUCCESSFULLY};
        Ofa2NicAsicBuff[self[2]] := Tail(Ofa2NicAsicBuff[self[2]]);

        SwitchNicAsicSendOutMsg:
            if swCanReceivePackets(self[2]) then
                switchWaitForLock();
                releaseLock(self);
                switch2Controller := Append(switch2Controller, egressMsg);
            else
                goto SwitchFromOFAPacket;
            end if;
    end while;
    end process
    
    fair process ofaModuleProcPacketIn \in ({OFA_IN} \X SW)
    variables ofaInMsg = NADIR_NULL
    begin
    SwitchOfaProcIn: 
    while TRUE do
        await swOFACanProcessIRs(self[2]);
        await Len(NicAsic2OfaBuff[self[2]]) > 0;
        switchAcquireLock();
        ofaInMsg := Head(NicAsic2OfaBuff[self[2]]);           
        assert ofaInMsg.to = self[2];
        assert ofaInMsg.type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM};
        
        NicAsic2OfaBuff[self[2]] := Tail(NicAsic2OfaBuff[self[2]]);

        SwitchOfaProcessPacket:
           if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<INSTALLER, self[2]>>);
                Ofa2InstallerBuff[self[2]] := Append(Ofa2InstallerBuff[self[2]], [type |-> ofaInMsg.type, 
                                                                                    flow |-> ofaInMsg.flow,
                                                                                    from |-> ofaInMsg.from]);
           else
                goto SwitchOfaProcIn;
           end if;
    end while    
    end process
    
    fair process ofaModuleProcPacketOut \in ({OFA_OUT} \X SW)
    variables ofaOutConfirmation = NADIR_NULL
    begin
    SwitchOfaProcOut:
    while TRUE do
        await swOFACanProcessIRs(self[2]);
        await Installer2OfaBuff[self[2]] # <<>>;
        switchAcquireLock();
        ofaOutConfirmation := Head(Installer2OfaBuff[self[2]]);
        Installer2OfaBuff[self[2]] := Tail(Installer2OfaBuff[self[2]]);
        assert ofaOutConfirmation.type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM};

        SendInstallationConfirmation:
            if swOFACanProcessIRs(self[2]) then
                acquireAndChangeLock(<<NIC_ASIC_OUT, self[2]>>);
                if ofaOutConfirmation.type = INSTALL_FLOW then
                    sendConfirmation(ofaOutConfirmation.from, ofaOutConfirmation.flow, INSTALLED_SUCCESSFULLY); 
                elsif ofaOutConfirmation.type = DELETE_FLOW then
                    sendConfirmation(ofaOutConfirmation.from, ofaOutConfirmation.flow, DELETED_SUCCESSFULLY); 
                else
                    sendClearConfirmation();
                end if;
            else 
                goto SwitchOfaProcOut;
            end if;                                                              
    end while;                                                                      
    end process

    fair process installerModuleProc \in ({INSTALLER} \X SW)
    variables installerInIR = NADIR_NULL
    begin
    SwitchInstallerProc: 
    while TRUE do     
       await swCanInstallIRs(self[2]);
       await Len(Ofa2InstallerBuff[self[2]]) > 0;
       switchAcquireLock();
       installerInIR := Head(Ofa2InstallerBuff[self[2]]);
       assert installerInIR.type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM};
       
       Ofa2InstallerBuff[self[2]] := Tail(Ofa2InstallerBuff[self[2]]);

       SwitchInstallerInsert2TCAM:
            if swCanInstallIRs(self[2]) then
                switchAcquireLock();
                if installerInIR.type = INSTALL_FLOW then    
                    installToTCAM(installerInIR.flow);
                elsif installerInIR.type = DELETE_FLOW then
                    removeFromTCAM(installerInIR.flow);
                else
                    clearTCAM();
                end if; 
            else
                goto SwitchInstallerProc;
            end if;

       SwitchInstallerSendConfirmation:
            if swCanInstallIRs(self[2]) then
                acquireAndChangeLock(<<OFA_OUT, self[2]>>);
                Installer2OfaBuff[self[2]] := Append(Installer2OfaBuff[self[2]], installerInIR);
            else
                goto SwitchInstallerProc;
            end if;
    end while;
    end process

    fair process swFailureProc \in ({SW_FAILURE_PROC} \X SW)
    variable statusMsg = <<>>, notFailedSet = {}, failedElem = "", obj = NADIR_NULL;
    begin
    SwitchFailure:
    while TRUE do
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                 \/ switchLock[2] = self[2];
        await sw_fail_ordering_var # <<>>;
        await \E x \in Head(sw_fail_ordering_var): x.sw = self[2];
        obj := CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2];
        RecoveryStatus[self[2]].transient := obj.transient || RecoveryStatus[self[2]].partial := obj.partial;
        removeFromSeqSet(sw_fail_ordering_var, obj);
        
        await pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure";
        
        if obj.partial = 0 then
            completeFailure();
        else
            notFailedSet := returnSwitchElementsNotFailed(self[2]);
            await notFailedSet # {};
            with elem \in notFailedSet do
                failedElem := elem;
            end with;
        
            if failedElem = "cpu" then
                cpuFailure();
            elsif failedElem = "ofa" then
                ofaFailure();
            elsif failedElem = "installer" then
                installerFailure();
            elsif failedElem = "nicAsic" then 
                nicAsicFailure();
            else assert FALSE;
            end if;
        end if;
    end while
    end process

    fair process swResolveFailure \in ({SW_RESOLVE_PROC} \X SW)
    variable failedSet = {}, statusResolveMsg = NADIR_NULL, recoveredElem = NADIR_NULL;
    begin
    SwitchResolveFailure:
    while TRUE do
        await RecoveryStatus[self[2]].transient = 1;
        await /\ controllerLock = <<NO_LOCK, NO_LOCK>>
              /\ switchLock = <<NO_LOCK, NO_LOCK>>;
              
        if RecoveryStatus[self[2]].partial = 0 then
            resolveCompleteFailure();
        else
            failedSet := returnSwitchFailedElements(self[2]);
            await Cardinality(failedSet) > 0;
            with elem \in failedSet do
                recoveredElem := elem;
            end with;
        
            if recoveredElem = "cpu" then resolveCpuFailure();
            elsif recoveredElem = "nicAsic" then resolveNicAsicFailure();
            elsif recoveredElem = "ofa" then resolveOfaFailure();
            elsif recoveredElem = "installer" then resolveInstallerFailure();
            else assert FALSE;
            end if;
        
        end if;
        
        RecoveryStatus[self[2]] := [transient |-> 0, partial |-> 0];
    end while
    end process

    fair process ghostUnlockProcess \in ({GHOST_UNLOCK_PROC} \X SW)
    begin
    ghostProc:
    while TRUE do
        await /\ switchLock # <<NO_LOCK, NO_LOCK>>
              /\ switchLock[2] = self[2]
              /\ controllerLock = <<NO_LOCK, NO_LOCK>>;
        if WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL then
            await switchStatus[switchLock[2]].nicAsic = Failed;
        else
            if switchStatus[switchLock[2]].cpu = Failed /\ switchLock[1] = NIC_ASIC_OUT then
                await pc[switchLock] = "SwitchFromOFAPacket";
            else
                if switchLock[1] \in {NIC_ASIC_IN, NIC_ASIC_OUT} then 
                    await switchStatus[switchLock[2]].nicAsic = Failed;
                    await /\ pc[<<NIC_ASIC_IN, self[2]>>] = "SwitchRcvPacket"
                          /\ pc[<<NIC_ASIC_OUT, self[2]>>] = "SwitchFromOFAPacket"; 
                elsif switchLock[1] \in {OFA_IN, OFA_OUT} then 
                    await switchStatus[switchLock[2]].ofa = Failed;
                    await /\ pc[<<OFA_IN, self[2]>>] = "SwitchOfaProcIn"
                          /\ pc[<<OFA_OUT, self[2]>>] = "SwitchOfaProcOut";
                elsif switchLock[1] \in {INSTALLER} then
                    await switchStatus[switchLock[2]].installer = Failed;
                    await pc[<<INSTALLER, self[2]>>] = "SwitchInstallerProc"; 
                end if;
            end if;
        end if;
        releaseLock(switchLock);
    end while
    end process
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "52b1be07" /\ chksum(tla) = "4c85fed")
VARIABLES switchLock, controllerLock, sw_fail_ordering_var, controller2Switch, 
          switch2Controller, switchStatus, installedIRs, NicAsic2OfaBuff, 
          Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff, TCAM, 
          controlMsgCounter, RecoveryStatus, pc

(* define statement *)
removeFromSeq(inSeq, RID) == [j \in 1..(Len(inSeq) - 1) |-> IF j < RID THEN inSeq[j]
                                                            ELSE inSeq[j+1]]

swCanReceivePackets(sw) == switchStatus[sw].nicAsic = NotFailed
swOFACanProcessIRs(sw) == /\ switchStatus[sw].cpu = NotFailed
                          /\ switchStatus[sw].ofa = NotFailed

existMatchingEntryTCAM(swID, flowID) == flowID \in TCAM[swID]
swCanInstallIRs(sw) == /\ switchStatus[sw].installer = NotFailed
                       /\ switchStatus[sw].cpu = NotFailed

returnSwitchElementsNotFailed(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = NotFailed
                                   /\ \/ /\ WHICH_SWITCH_MODEL[x] = SW_COMPLEX_MODEL
                                         /\ SW_MODULE_CAN_FAIL_OR_NOT[x] = 1
                                      \/ /\ WHICH_SWITCH_MODEL[x] = SW_SIMPLE_MODEL
                                         /\ x = "nicAsic"
}
returnSwitchFailedElements(sw) == {
    x \in DOMAIN switchStatus[sw]: /\ switchStatus[sw][x] = Failed
                                   /\ \/ switchStatus[sw].cpu = NotFailed
                                      \/ x \notin {"ofa", "installer"}
}
installerInStartingMode(swID) == pc[<<INSTALLER, swID>>] = "SwitchInstallerProc"
ofaStartingMode(swID) == /\ pc[<<OFA_IN, swID>>] = "SwitchOfaProcIn"
                         /\ pc[<<OFA_OUT, swID>>] = "SwitchOfaProcOut"
nicAsicStartingMode(swID) == /\ pc[<<NIC_ASIC_IN, swID>>] = "SwitchRcvPacket"
                             /\ pc[<<NIC_ASIC_OUT, swID>>] = "SwitchFromOFAPacket"
getInstallerStatus(stat) == IF stat = NotFailed
                            THEN INSTALLER_UP
                            ELSE INSTALLER_DOWN

VARIABLES ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, statusMsg, notFailedSet, failedElem, obj, failedSet, 
          statusResolveMsg, recoveredElem

vars == << switchLock, controllerLock, sw_fail_ordering_var, 
           controller2Switch, switch2Controller, switchStatus, installedIRs, 
           NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, 
           Ofa2InstallerBuff, TCAM, controlMsgCounter, RecoveryStatus, pc, 
           ingressPkt, ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
           installerInIR, statusMsg, notFailedSet, failedElem, obj, failedSet, 
           statusResolveMsg, recoveredElem >>

ProcSet == (({SW_SIMPLE_ID} \X SW)) \cup (({NIC_ASIC_IN} \X SW)) \cup (({NIC_ASIC_OUT} \X SW)) \cup (({OFA_IN} \X SW)) \cup (({OFA_OUT} \X SW)) \cup (({INSTALLER} \X SW)) \cup (({SW_FAILURE_PROC} \X SW)) \cup (({SW_RESOLVE_PROC} \X SW)) \cup (({GHOST_UNLOCK_PROC} \X SW))

Init == (* Global variables *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        /\ switchStatus =                [
                              x \in SW |-> [
                                  cpu |-> NotFailed,
                                  nicAsic |-> NotFailed,
                                  ofa |-> NotFailed,
                                  installer |-> NotFailed
                              ]
                          ]
        /\ installedIRs = <<>>
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> {}]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        (* Process swProcess *)
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> NADIR_NULL]
        (* Process swNicAsicProcPacketIn *)
        /\ ingressIR = [self \in ({NIC_ASIC_IN} \X SW) |-> NADIR_NULL]
        (* Process swNicAsicProcPacketOut *)
        /\ egressMsg = [self \in ({NIC_ASIC_OUT} \X SW) |-> NADIR_NULL]
        (* Process ofaModuleProcPacketIn *)
        /\ ofaInMsg = [self \in ({OFA_IN} \X SW) |-> NADIR_NULL]
        (* Process ofaModuleProcPacketOut *)
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> NADIR_NULL]
        (* Process installerModuleProc *)
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> NADIR_NULL]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> <<>>]
        /\ notFailedSet = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ failedElem = [self \in ({SW_FAILURE_PROC} \X SW) |-> ""]
        /\ obj = [self \in ({SW_FAILURE_PROC} \X SW) |-> NADIR_NULL]
        (* Process swResolveFailure *)
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> NADIR_NULL]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> NADIR_NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({NIC_ASIC_IN} \X SW) -> "SwitchRcvPacket"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchFromOFAPacket"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaProcIn"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaProcOut"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerProc"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"]

SwitchSimpleProcess(self) == /\ pc[self] = "SwitchSimpleProcess"
                             /\ whichSwitchModel(self[2]) = SW_SIMPLE_MODEL
                             /\ swCanReceivePackets(self[2])
                             /\ Len(controller2Switch[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ ingressPkt' = [ingressPkt EXCEPT ![self] = Head(controller2Switch[self[2]])]
                             /\ Assert(ingressPkt'[self].type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}, 
                                       "Failure of assertion at line 380, column 9.")
                             /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                             /\ IF ingressPkt'[self].type = INSTALL_FLOW
                                   THEN /\ installedIRs' = Append(installedIRs, (ingressPkt'[self].flow))
                                        /\ TCAM' = [TCAM EXCEPT ![self[2]] = TCAM[self[2]] \cup {(ingressPkt'[self].flow)}]
                                        /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                              THEN /\ switch2Controller' = Append(switch2Controller, (           [
                                                                               type |-> INSTALLED_SUCCESSFULLY,
                                                                               from |-> self[2],
                                                                               to |-> (ingressPkt'[self].from),
                                                                               flow |-> (ingressPkt'[self].flow)
                                                                           ]))
                                                   /\ UNCHANGED Ofa2NicAsicBuff
                                              ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], (           [
                                                                                                                  type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                  from |-> self[2],
                                                                                                                  to |-> (ingressPkt'[self].from),
                                                                                                                  flow |-> (ingressPkt'[self].flow)
                                                                                                              ]))]
                                                   /\ UNCHANGED switch2Controller
                                        /\ UNCHANGED controlMsgCounter
                                   ELSE /\ IF ingressPkt'[self].type = DELETE_FLOW
                                              THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = (TCAM[self[2]] \ {(ingressPkt'[self].flow)})]
                                                   /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                         THEN /\ switch2Controller' = Append(switch2Controller, (           [
                                                                                          type |-> DELETED_SUCCESSFULLY,
                                                                                          from |-> self[2],
                                                                                          to |-> (ingressPkt'[self].from),
                                                                                          flow |-> (ingressPkt'[self].flow)
                                                                                      ]))
                                                              /\ UNCHANGED Ofa2NicAsicBuff
                                                         ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], (           [
                                                                                                                             type |-> DELETED_SUCCESSFULLY,
                                                                                                                             from |-> self[2],
                                                                                                                             to |-> (ingressPkt'[self].from),
                                                                                                                             flow |-> (ingressPkt'[self].flow)
                                                                                                                         ]))]
                                                              /\ UNCHANGED switch2Controller
                                                   /\ UNCHANGED controlMsgCounter
                                              ELSE /\ IF ingressPkt'[self].type = CLEAR_TCAM
                                                         THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                              /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                    THEN /\ switch2Controller' =                      Append(
                                                                                                     switch2Controller,
                                                                                                     [
                                                                                                         type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                                                                         swID |-> self[2],
                                                                                                         num |-> controlMsgCounter'[self[2]],
                                                                                                         installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                                                                                                     ]
                                                                                                 )
                                                                         /\ UNCHANGED Ofa2NicAsicBuff
                                                                    ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] =                             Append(
                                                                                                                                        Ofa2NicAsicBuff[self[2]],
                                                                                                                                        [
                                                                                                                                            type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                                                                                                            swID |-> self[2],
                                                                                                                                            num |-> controlMsgCounter'[self[2]],
                                                                                                                                            installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                                                                                                                                        ]
                                                                                                                                    )]
                                                                         /\ UNCHANGED switch2Controller
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << switch2Controller, 
                                                                              Ofa2NicAsicBuff, 
                                                                              TCAM, 
                                                                              controlMsgCounter >>
                                        /\ UNCHANGED installedIRs
                             /\ Assert(\/ switchLock[2] = self[2]
                                       \/ switchLock[2] = NO_LOCK, 
                                       "Failure of assertion at line 361, column 9 of macro called at line 392, column 9.")
                             /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                             /\ pc' = [pc EXCEPT ![self] = "SwitchSimpleProcess"]
                             /\ UNCHANGED << controllerLock, 
                                             sw_fail_ordering_var, 
                                             switchStatus, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, RecoveryStatus, 
                                             ingressIR, egressMsg, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem >>

swProcess(self) == SwitchSimpleProcess(self)

SwitchRcvPacket(self) == /\ pc[self] = "SwitchRcvPacket"
                         /\ whichSwitchModel(self[2]) = SW_COMPLEX_MODEL
                         /\ swCanReceivePackets(self[2])
                         /\ Len(controller2Switch[self[2]]) > 0
                         /\ ingressIR' = [ingressIR EXCEPT ![self] = Head(controller2Switch[self[2]])]
                         /\ Assert(ingressIR'[self].type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}, 
                                   "Failure of assertion at line 409, column 9.")
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = Tail(controller2Switch[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicInsertToOfaBuff"]
                         /\ UNCHANGED << controllerLock, sw_fail_ordering_var, 
                                         switch2Controller, switchStatus, 
                                         installedIRs, NicAsic2OfaBuff, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         ingressPkt, egressMsg, ofaInMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem >>

SwitchNicAsicInsertToOfaBuff(self) == /\ pc[self] = "SwitchNicAsicInsertToOfaBuff"
                                      /\ IF swCanReceivePackets(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                 /\ switchLock' = <<OFA_IN, self[2]>>
                                                 /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Append(NicAsic2OfaBuff[self[2]], ingressIR[self])]
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchRcvPacket"]
                                                 /\ UNCHANGED << switchLock, 
                                                                 NicAsic2OfaBuff >>
                                      /\ UNCHANGED << controllerLock, 
                                                      sw_fail_ordering_var, 
                                                      controller2Switch, 
                                                      switch2Controller, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      Ofa2NicAsicBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      controlMsgCounter, 
                                                      RecoveryStatus, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem >>

swNicAsicProcPacketIn(self) == SwitchRcvPacket(self)
                                  \/ SwitchNicAsicInsertToOfaBuff(self)

SwitchFromOFAPacket(self) == /\ pc[self] = "SwitchFromOFAPacket"
                             /\ swCanReceivePackets(self[2])
                             /\ Len(Ofa2NicAsicBuff[self[2]]) > 0
                             /\ egressMsg' = [egressMsg EXCEPT ![self] = Head(Ofa2NicAsicBuff[self[2]])]
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ switchLock' = self
                             /\ Assert(egressMsg'[self].type \in {INSTALLED_SUCCESSFULLY,
                                                                  DELETED_SUCCESSFULLY,
                                                                  CLEARED_TCAM_SUCCESSFULLY}, 
                                       "Failure of assertion at line 432, column 9.")
                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Tail(Ofa2NicAsicBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchNicAsicSendOutMsg"]
                             /\ UNCHANGED << controllerLock, 
                                             sw_fail_ordering_var, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Installer2OfaBuff, 
                                             Ofa2InstallerBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             ingressPkt, ingressIR, ofaInMsg, 
                                             ofaOutConfirmation, installerInIR, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem >>

SwitchNicAsicSendOutMsg(self) == /\ pc[self] = "SwitchNicAsicSendOutMsg"
                                 /\ IF swCanReceivePackets(self[2])
                                       THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                            /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                            /\ Assert(\/ switchLock[2] = self[2]
                                                      \/ switchLock[2] = NO_LOCK, 
                                                      "Failure of assertion at line 361, column 9 of macro called at line 440, column 17.")
                                            /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                                            /\ switch2Controller' = Append(switch2Controller, egressMsg[self])
                                            /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchFromOFAPacket"]
                                            /\ UNCHANGED << switchLock, 
                                                            switch2Controller >>
                                 /\ UNCHANGED << controllerLock, 
                                                 sw_fail_ordering_var, 
                                                 controller2Switch, 
                                                 switchStatus, installedIRs, 
                                                 NicAsic2OfaBuff, 
                                                 Ofa2NicAsicBuff, 
                                                 Installer2OfaBuff, 
                                                 Ofa2InstallerBuff, TCAM, 
                                                 controlMsgCounter, 
                                                 RecoveryStatus, ingressPkt, 
                                                 ingressIR, egressMsg, 
                                                 ofaInMsg, ofaOutConfirmation, 
                                                 installerInIR, statusMsg, 
                                                 notFailedSet, failedElem, obj, 
                                                 failedSet, statusResolveMsg, 
                                                 recoveredElem >>

swNicAsicProcPacketOut(self) == SwitchFromOFAPacket(self)
                                   \/ SwitchNicAsicSendOutMsg(self)

SwitchOfaProcIn(self) == /\ pc[self] = "SwitchOfaProcIn"
                         /\ swOFACanProcessIRs(self[2])
                         /\ Len(NicAsic2OfaBuff[self[2]]) > 0
                         /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                         /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                         /\ switchLock' = self
                         /\ ofaInMsg' = [ofaInMsg EXCEPT ![self] = Head(NicAsic2OfaBuff[self[2]])]
                         /\ Assert(ofaInMsg'[self].to = self[2], 
                                   "Failure of assertion at line 457, column 9.")
                         /\ Assert(ofaInMsg'[self].type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}, 
                                   "Failure of assertion at line 458, column 9.")
                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = Tail(NicAsic2OfaBuff[self[2]])]
                         /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcessPacket"]
                         /\ UNCHANGED << controllerLock, sw_fail_ordering_var, 
                                         controller2Switch, switch2Controller, 
                                         switchStatus, installedIRs, 
                                         Ofa2NicAsicBuff, Installer2OfaBuff, 
                                         Ofa2InstallerBuff, TCAM, 
                                         controlMsgCounter, RecoveryStatus, 
                                         ingressPkt, ingressIR, egressMsg, 
                                         ofaOutConfirmation, installerInIR, 
                                         statusMsg, notFailedSet, failedElem, 
                                         obj, failedSet, statusResolveMsg, 
                                         recoveredElem >>

SwitchOfaProcessPacket(self) == /\ pc[self] = "SwitchOfaProcessPacket"
                                /\ IF swOFACanProcessIRs(self[2])
                                      THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                           /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                           /\ switchLock' = <<INSTALLER, self[2]>>
                                           /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Append(Ofa2InstallerBuff[self[2]], [type |-> ofaInMsg[self].type,
                                                                                                                                                flow |-> ofaInMsg[self].flow,
                                                                                                                                                from |-> ofaInMsg[self].from])]
                                           /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcIn"]
                                           /\ UNCHANGED << switchLock, 
                                                           Ofa2InstallerBuff >>
                                /\ UNCHANGED << controllerLock, 
                                                sw_fail_ordering_var, 
                                                controller2Switch, 
                                                switch2Controller, 
                                                switchStatus, installedIRs, 
                                                NicAsic2OfaBuff, 
                                                Ofa2NicAsicBuff, 
                                                Installer2OfaBuff, TCAM, 
                                                controlMsgCounter, 
                                                RecoveryStatus, ingressPkt, 
                                                ingressIR, egressMsg, ofaInMsg, 
                                                ofaOutConfirmation, 
                                                installerInIR, statusMsg, 
                                                notFailedSet, failedElem, obj, 
                                                failedSet, statusResolveMsg, 
                                                recoveredElem >>

ofaModuleProcPacketIn(self) == SwitchOfaProcIn(self)
                                  \/ SwitchOfaProcessPacket(self)

SwitchOfaProcOut(self) == /\ pc[self] = "SwitchOfaProcOut"
                          /\ swOFACanProcessIRs(self[2])
                          /\ Installer2OfaBuff[self[2]] # <<>>
                          /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                          /\ switchLock' = self
                          /\ ofaOutConfirmation' = [ofaOutConfirmation EXCEPT ![self] = Head(Installer2OfaBuff[self[2]])]
                          /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Tail(Installer2OfaBuff[self[2]])]
                          /\ Assert(ofaOutConfirmation'[self].type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}, 
                                    "Failure of assertion at line 484, column 9.")
                          /\ pc' = [pc EXCEPT ![self] = "SendInstallationConfirmation"]
                          /\ UNCHANGED << controllerLock, sw_fail_ordering_var, 
                                          controller2Switch, switch2Controller, 
                                          switchStatus, installedIRs, 
                                          NicAsic2OfaBuff, Ofa2NicAsicBuff, 
                                          Ofa2InstallerBuff, TCAM, 
                                          controlMsgCounter, RecoveryStatus, 
                                          ingressPkt, ingressIR, egressMsg, 
                                          ofaInMsg, installerInIR, statusMsg, 
                                          notFailedSet, failedElem, obj, 
                                          failedSet, statusResolveMsg, 
                                          recoveredElem >>

SendInstallationConfirmation(self) == /\ pc[self] = "SendInstallationConfirmation"
                                      /\ IF swOFACanProcessIRs(self[2])
                                            THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                 /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                 /\ switchLock' = <<NIC_ASIC_OUT, self[2]>>
                                                 /\ IF ofaOutConfirmation[self].type = INSTALL_FLOW
                                                       THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                  THEN /\ switch2Controller' = Append(switch2Controller, (           [
                                                                                                   type |-> INSTALLED_SUCCESSFULLY,
                                                                                                   from |-> self[2],
                                                                                                   to |-> (ofaOutConfirmation[self].from),
                                                                                                   flow |-> (ofaOutConfirmation[self].flow)
                                                                                               ]))
                                                                       /\ UNCHANGED Ofa2NicAsicBuff
                                                                  ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], (           [
                                                                                                                                      type |-> INSTALLED_SUCCESSFULLY,
                                                                                                                                      from |-> self[2],
                                                                                                                                      to |-> (ofaOutConfirmation[self].from),
                                                                                                                                      flow |-> (ofaOutConfirmation[self].flow)
                                                                                                                                  ]))]
                                                                       /\ UNCHANGED switch2Controller
                                                            /\ UNCHANGED controlMsgCounter
                                                       ELSE /\ IF ofaOutConfirmation[self].type = DELETE_FLOW
                                                                  THEN /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                             THEN /\ switch2Controller' = Append(switch2Controller, (           [
                                                                                                              type |-> DELETED_SUCCESSFULLY,
                                                                                                              from |-> self[2],
                                                                                                              to |-> (ofaOutConfirmation[self].from),
                                                                                                              flow |-> (ofaOutConfirmation[self].flow)
                                                                                                          ]))
                                                                                  /\ UNCHANGED Ofa2NicAsicBuff
                                                                             ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = Append(Ofa2NicAsicBuff[self[2]], (           [
                                                                                                                                                 type |-> DELETED_SUCCESSFULLY,
                                                                                                                                                 from |-> self[2],
                                                                                                                                                 to |-> (ofaOutConfirmation[self].from),
                                                                                                                                                 flow |-> (ofaOutConfirmation[self].flow)
                                                                                                                                             ]))]
                                                                                  /\ UNCHANGED switch2Controller
                                                                       /\ UNCHANGED controlMsgCounter
                                                                  ELSE /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                       /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                                                                             THEN /\ switch2Controller' =                      Append(
                                                                                                              switch2Controller,
                                                                                                              [
                                                                                                                  type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                                                                                  swID |-> self[2],
                                                                                                                  num |-> controlMsgCounter'[self[2]],
                                                                                                                  installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                                                                                                              ]
                                                                                                          )
                                                                                  /\ UNCHANGED Ofa2NicAsicBuff
                                                                             ELSE /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] =                             Append(
                                                                                                                                                 Ofa2NicAsicBuff[self[2]],
                                                                                                                                                 [
                                                                                                                                                     type |-> CLEARED_TCAM_SUCCESSFULLY,
                                                                                                                                                     swID |-> self[2],
                                                                                                                                                     num |-> controlMsgCounter'[self[2]],
                                                                                                                                                     installerStatus |-> getInstallerStatus(switchStatus[self[2]].installer)
                                                                                                                                                 ]
                                                                                                                                             )]
                                                                                  /\ UNCHANGED switch2Controller
                                                 /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchOfaProcOut"]
                                                 /\ UNCHANGED << switchLock, 
                                                                 switch2Controller, 
                                                                 Ofa2NicAsicBuff, 
                                                                 controlMsgCounter >>
                                      /\ UNCHANGED << controllerLock, 
                                                      sw_fail_ordering_var, 
                                                      controller2Switch, 
                                                      switchStatus, 
                                                      installedIRs, 
                                                      NicAsic2OfaBuff, 
                                                      Installer2OfaBuff, 
                                                      Ofa2InstallerBuff, TCAM, 
                                                      RecoveryStatus, 
                                                      ingressPkt, ingressIR, 
                                                      egressMsg, ofaInMsg, 
                                                      ofaOutConfirmation, 
                                                      installerInIR, statusMsg, 
                                                      notFailedSet, failedElem, 
                                                      obj, failedSet, 
                                                      statusResolveMsg, 
                                                      recoveredElem >>

ofaModuleProcPacketOut(self) == SwitchOfaProcOut(self)
                                   \/ SendInstallationConfirmation(self)

SwitchInstallerProc(self) == /\ pc[self] = "SwitchInstallerProc"
                             /\ swCanInstallIRs(self[2])
                             /\ Len(Ofa2InstallerBuff[self[2]]) > 0
                             /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                             /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                             /\ switchLock' = self
                             /\ installerInIR' = [installerInIR EXCEPT ![self] = Head(Ofa2InstallerBuff[self[2]])]
                             /\ Assert(installerInIR'[self].type \in {INSTALL_FLOW, DELETE_FLOW, CLEAR_TCAM}, 
                                       "Failure of assertion at line 511, column 8.")
                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = Tail(Ofa2InstallerBuff[self[2]])]
                             /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerInsert2TCAM"]
                             /\ UNCHANGED << controllerLock, 
                                             sw_fail_ordering_var, 
                                             controller2Switch, 
                                             switch2Controller, switchStatus, 
                                             installedIRs, NicAsic2OfaBuff, 
                                             Ofa2NicAsicBuff, 
                                             Installer2OfaBuff, TCAM, 
                                             controlMsgCounter, RecoveryStatus, 
                                             ingressPkt, ingressIR, egressMsg, 
                                             ofaInMsg, ofaOutConfirmation, 
                                             statusMsg, notFailedSet, 
                                             failedElem, obj, failedSet, 
                                             statusResolveMsg, recoveredElem >>

SwitchInstallerInsert2TCAM(self) == /\ pc[self] = "SwitchInstallerInsert2TCAM"
                                    /\ IF swCanInstallIRs(self[2])
                                          THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                               /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                               /\ switchLock' = self
                                               /\ IF installerInIR[self].type = INSTALL_FLOW
                                                     THEN /\ installedIRs' = Append(installedIRs, (installerInIR[self].flow))
                                                          /\ TCAM' = [TCAM EXCEPT ![self[2]] = TCAM[self[2]] \cup {(installerInIR[self].flow)}]
                                                     ELSE /\ IF installerInIR[self].type = DELETE_FLOW
                                                                THEN /\ TCAM' = [TCAM EXCEPT ![self[2]] = (TCAM[self[2]] \ {(installerInIR[self].flow)})]
                                                                ELSE /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                                                          /\ UNCHANGED installedIRs
                                               /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerSendConfirmation"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                               /\ UNCHANGED << switchLock, 
                                                               installedIRs, 
                                                               TCAM >>
                                    /\ UNCHANGED << controllerLock, 
                                                    sw_fail_ordering_var, 
                                                    controller2Switch, 
                                                    switch2Controller, 
                                                    switchStatus, 
                                                    NicAsic2OfaBuff, 
                                                    Ofa2NicAsicBuff, 
                                                    Installer2OfaBuff, 
                                                    Ofa2InstallerBuff, 
                                                    controlMsgCounter, 
                                                    RecoveryStatus, ingressPkt, 
                                                    ingressIR, egressMsg, 
                                                    ofaInMsg, 
                                                    ofaOutConfirmation, 
                                                    installerInIR, statusMsg, 
                                                    notFailedSet, failedElem, 
                                                    obj, failedSet, 
                                                    statusResolveMsg, 
                                                    recoveredElem >>

SwitchInstallerSendConfirmation(self) == /\ pc[self] = "SwitchInstallerSendConfirmation"
                                         /\ IF swCanInstallIRs(self[2])
                                               THEN /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                                    /\ switchLock \in {<<NO_LOCK, NO_LOCK>>, self}
                                                    /\ switchLock' = <<OFA_OUT, self[2]>>
                                                    /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = Append(Installer2OfaBuff[self[2]], installerInIR[self])]
                                                    /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchInstallerProc"]
                                                    /\ UNCHANGED << switchLock, 
                                                                    Installer2OfaBuff >>
                                         /\ UNCHANGED << controllerLock, 
                                                         sw_fail_ordering_var, 
                                                         controller2Switch, 
                                                         switch2Controller, 
                                                         switchStatus, 
                                                         installedIRs, 
                                                         NicAsic2OfaBuff, 
                                                         Ofa2NicAsicBuff, 
                                                         Ofa2InstallerBuff, 
                                                         TCAM, 
                                                         controlMsgCounter, 
                                                         RecoveryStatus, 
                                                         ingressPkt, ingressIR, 
                                                         egressMsg, ofaInMsg, 
                                                         ofaOutConfirmation, 
                                                         installerInIR, 
                                                         statusMsg, 
                                                         notFailedSet, 
                                                         failedElem, obj, 
                                                         failedSet, 
                                                         statusResolveMsg, 
                                                         recoveredElem >>

installerModuleProc(self) == SwitchInstallerProc(self)
                                \/ SwitchInstallerInsert2TCAM(self)
                                \/ SwitchInstallerSendConfirmation(self)

SwitchFailure(self) == /\ pc[self] = "SwitchFailure"
                       /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                          /\ \/ switchLock = <<NO_LOCK, NO_LOCK>>
                             \/ switchLock[2] = self[2]
                       /\ sw_fail_ordering_var # <<>>
                       /\ \E x \in Head(sw_fail_ordering_var): x.sw = self[2]
                       /\ obj' = [obj EXCEPT ![self] = CHOOSE x \in Head(sw_fail_ordering_var): x.sw = self[2]]
                       /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]].transient = obj'[self].transient,
                                                                   ![self[2]].partial = obj'[self].partial]
                       /\ Assert(obj'[self] \in Head(sw_fail_ordering_var), 
                                 "Failure of assertion at line 71, column 9 of macro called at line 551, column 9.")
                       /\ IF Cardinality(Head(sw_fail_ordering_var)) = 1
                             THEN /\ sw_fail_ordering_var' = Tail(sw_fail_ordering_var)
                             ELSE /\ sw_fail_ordering_var' = <<(Head(sw_fail_ordering_var)\{obj'[self]})>> \o Tail(sw_fail_ordering_var)
                       /\ pc[<<SW_RESOLVE_PROC, self[2]>>] = "SwitchResolveFailure"
                       /\ IF obj'[self].partial = 0
                             THEN /\ IF switchStatus[self[2]].nicAsic = NotFailed
                                        THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                             /\ statusMsg' = [statusMsg EXCEPT ![self] = [type |-> NIC_ASIC_DOWN,
                                                                                            swID |-> self[2],
                                                                                            num |-> controlMsgCounter'[self[2]]]]
                                             /\ switch2Controller' = Append(switch2Controller, statusMsg'[self])
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << switch2Controller, 
                                                             controlMsgCounter, 
                                                             statusMsg >>
                                  /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> Failed, nicAsic |-> Failed,
                                                                                          ofa |-> Failed, installer |-> Failed]]
                                  /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                  /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                  /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                                  /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                  /\ UNCHANGED << notFailedSet, failedElem >>
                             ELSE /\ notFailedSet' = [notFailedSet EXCEPT ![self] = returnSwitchElementsNotFailed(self[2])]
                                  /\ notFailedSet'[self] # {}
                                  /\ \E elem \in notFailedSet'[self]:
                                       failedElem' = [failedElem EXCEPT ![self] = elem]
                                  /\ IF failedElem'[self] = "cpu"
                                        THEN /\ Assert(switchStatus[self[2]].cpu = NotFailed, 
                                                       "Failure of assertion at line 173, column 9 of macro called at line 565, column 17.")
                                             /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = Failed,
                                                                                     ![self[2]].ofa = Failed,
                                                                                     ![self[2]].installer = Failed]
                                             /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                             /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                             /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                             /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                             /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                   THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                        /\ statusMsg' = [statusMsg EXCEPT ![self] =              [
                                                                                                        type |-> OFA_DOWN,
                                                                                                        swID |-> self[2],
                                                                                                        num |-> controlMsgCounter'[self[2]]
                                                                                                    ]]
                                                        /\ switch2Controller' = Append(switch2Controller, statusMsg'[self])
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << switch2Controller, 
                                                                        controlMsgCounter, 
                                                                        statusMsg >>
                                             /\ UNCHANGED controller2Switch
                                        ELSE /\ IF failedElem'[self] = "ofa"
                                                   THEN /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = NotFailed, 
                                                                  "Failure of assertion at line 213, column 9 of macro called at line 567, column 17.")
                                                        /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = Failed]
                                                        /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                              THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                   /\ statusMsg' = [statusMsg EXCEPT ![self] =              [
                                                                                                                   type |-> OFA_DOWN,
                                                                                                                   swID |-> self[2],
                                                                                                                   num |-> controlMsgCounter'[self[2]]
                                                                                                               ]]
                                                                   /\ switch2Controller' = Append(switch2Controller, statusMsg'[self])
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << switch2Controller, 
                                                                                   controlMsgCounter, 
                                                                                   statusMsg >>
                                                        /\ UNCHANGED controller2Switch
                                                   ELSE /\ IF failedElem'[self] = "installer"
                                                              THEN /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = NotFailed, 
                                                                             "Failure of assertion at line 245, column 9 of macro called at line 569, column 17.")
                                                                   /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = Failed]
                                                                   /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                         THEN /\ Assert(switchStatus'[self[2]].installer = Failed, 
                                                                                        "Failure of assertion at line 248, column 13 of macro called at line 569, column 17.")
                                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                              /\ statusMsg' = [statusMsg EXCEPT ![self] =              [
                                                                                                                              type |-> KEEP_ALIVE,
                                                                                                                              swID |-> self[2],
                                                                                                                              num |-> controlMsgCounter'[self[2]],
                                                                                                                              installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                                                          ]]
                                                                              /\ switch2Controller' = Append(switch2Controller, statusMsg'[self])
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED << switch2Controller, 
                                                                                              controlMsgCounter, 
                                                                                              statusMsg >>
                                                                   /\ UNCHANGED controller2Switch
                                                              ELSE /\ IF failedElem'[self] = "nicAsic"
                                                                         THEN /\ Assert(switchStatus[self[2]].nicAsic = NotFailed, 
                                                                                        "Failure of assertion at line 134, column 9 of macro called at line 571, column 17.")
                                                                              /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = Failed]
                                                                              /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                                              /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                              /\ statusMsg' = [statusMsg EXCEPT ![self] =              [
                                                                                                                              type |-> NIC_ASIC_DOWN,
                                                                                                                              swID |-> self[2],
                                                                                                                              num |-> controlMsgCounter'[self[2]]
                                                                                                                          ]]
                                                                              /\ switch2Controller' = Append(switch2Controller, statusMsg'[self])
                                                                         ELSE /\ Assert(FALSE, 
                                                                                        "Failure of assertion at line 572, column 18.")
                                                                              /\ UNCHANGED << controller2Switch, 
                                                                                              switch2Controller, 
                                                                                              switchStatus, 
                                                                                              controlMsgCounter, 
                                                                                              statusMsg >>
                                             /\ UNCHANGED << NicAsic2OfaBuff, 
                                                             Ofa2NicAsicBuff, 
                                                             Installer2OfaBuff, 
                                                             Ofa2InstallerBuff >>
                                  /\ TCAM' = TCAM
                       /\ pc' = [pc EXCEPT ![self] = "SwitchFailure"]
                       /\ UNCHANGED << switchLock, controllerLock, 
                                       installedIRs, ingressPkt, ingressIR, 
                                       egressMsg, ofaInMsg, ofaOutConfirmation, 
                                       installerInIR, failedSet, 
                                       statusResolveMsg, recoveredElem >>

swFailureProc(self) == SwitchFailure(self)

SwitchResolveFailure(self) == /\ pc[self] = "SwitchResolveFailure"
                              /\ RecoveryStatus[self[2]].transient = 1
                              /\ /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                                 /\ switchLock = <<NO_LOCK, NO_LOCK>>
                              /\ IF RecoveryStatus[self[2]].partial = 0
                                    THEN /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                   "Failure of assertion at line 104, column 9 of macro called at line 588, column 13.")
                                         /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                   "Failure of assertion at line 105, column 9 of macro called at line 588, column 13.")
                                         /\ Assert(switchStatus[self[2]].ofa = Failed, 
                                                   "Failure of assertion at line 106, column 9 of macro called at line 588, column 13.")
                                         /\ Assert(switchStatus[self[2]].installer = Failed, 
                                                   "Failure of assertion at line 107, column 9 of macro called at line 588, column 13.")
                                         /\ nicAsicStartingMode(self[2])
                                         /\ ofaStartingMode(self[2])
                                         /\ installerInStartingMode(self[2])
                                         /\ switchStatus' = [switchStatus EXCEPT ![self[2]] = [cpu |-> NotFailed, nicAsic |-> NotFailed,
                                                                                                 ofa |-> NotFailed, installer |-> NotFailed]]
                                         /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                         /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                         /\ TCAM' = [TCAM EXCEPT ![self[2]] = {}]
                                         /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                         /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                         /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                                       type |-> KEEP_ALIVE,
                                                                                                       swID |-> self[2],
                                                                                                       num |-> controlMsgCounter'[self[2]],
                                                                                                       installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                                   ]]
                                         /\ switch2Controller' = Append(switch2Controller, statusResolveMsg'[self])
                                         /\ UNCHANGED << failedSet, 
                                                         recoveredElem >>
                                    ELSE /\ failedSet' = [failedSet EXCEPT ![self] = returnSwitchFailedElements(self[2])]
                                         /\ Cardinality(failedSet'[self]) > 0
                                         /\ \E elem \in failedSet'[self]:
                                              recoveredElem' = [recoveredElem EXCEPT ![self] = elem]
                                         /\ IF recoveredElem'[self] = "cpu"
                                               THEN /\ ofaStartingMode(self[2]) /\ installerInStartingMode(self[2])
                                                    /\ Assert(switchStatus[self[2]].cpu = Failed, 
                                                              "Failure of assertion at line 193, column 9 of macro called at line 596, column 43.")
                                                    /\ switchStatus' = [switchStatus EXCEPT ![self[2]].cpu = NotFailed,
                                                                                            ![self[2]].ofa = NotFailed,
                                                                                            ![self[2]].installer = NotFailed]
                                                    /\ NicAsic2OfaBuff' = [NicAsic2OfaBuff EXCEPT ![self[2]] = <<>>]
                                                    /\ Ofa2InstallerBuff' = [Ofa2InstallerBuff EXCEPT ![self[2]] = <<>>]
                                                    /\ Installer2OfaBuff' = [Installer2OfaBuff EXCEPT ![self[2]] = <<>>]
                                                    /\ Ofa2NicAsicBuff' = [Ofa2NicAsicBuff EXCEPT ![self[2]] = <<>>]
                                                    /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                          THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                               /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                                                             type |-> KEEP_ALIVE,
                                                                                                                             swID |-> self[2],
                                                                                                                             num |-> controlMsgCounter'[self[2]],
                                                                                                                             installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                                                         ]]
                                                               /\ switch2Controller' = Append(switch2Controller, statusResolveMsg'[self])
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED << switch2Controller, 
                                                                               controlMsgCounter, 
                                                                               statusResolveMsg >>
                                                    /\ UNCHANGED controller2Switch
                                               ELSE /\ IF recoveredElem'[self] = "nicAsic"
                                                          THEN /\ nicAsicStartingMode(self[2])
                                                               /\ Assert(switchStatus[self[2]].nicAsic = Failed, 
                                                                         "Failure of assertion at line 149, column 9 of macro called at line 597, column 50.")
                                                               /\ switchStatus' = [switchStatus EXCEPT ![self[2]].nicAsic = NotFailed]
                                                               /\ controller2Switch' = [controller2Switch EXCEPT ![self[2]] = <<>>]
                                                               /\ IF switchStatus'[self[2]].ofa = Failed
                                                                     THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                                                                        type |-> OFA_DOWN,
                                                                                                                                        swID |-> self[2],
                                                                                                                                        num |-> controlMsgCounter'[self[2]]
                                                                                                                                    ]]
                                                                     ELSE /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                          /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                                                                        type |-> KEEP_ALIVE,
                                                                                                                                        swID |-> self[2],
                                                                                                                                        num |-> controlMsgCounter'[self[2]],
                                                                                                                                        installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                                                                    ]]
                                                               /\ switch2Controller' = Append(switch2Controller, statusResolveMsg'[self])
                                                          ELSE /\ IF recoveredElem'[self] = "ofa"
                                                                     THEN /\ ofaStartingMode(self[2])
                                                                          /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].ofa = Failed, 
                                                                                    "Failure of assertion at line 229, column 9 of macro called at line 598, column 46.")
                                                                          /\ switchStatus' = [switchStatus EXCEPT ![self[2]].ofa = NotFailed]
                                                                          /\ IF switchStatus'[self[2]].nicAsic = NotFailed
                                                                                THEN /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                                     /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                                                                                   type |-> KEEP_ALIVE,
                                                                                                                                                   swID |-> self[2],
                                                                                                                                                   num |-> controlMsgCounter'[self[2]],
                                                                                                                                                   installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                                                                               ]]
                                                                                     /\ switch2Controller' = Append(switch2Controller, statusResolveMsg'[self])
                                                                                ELSE /\ TRUE
                                                                                     /\ UNCHANGED << switch2Controller, 
                                                                                                     controlMsgCounter, 
                                                                                                     statusResolveMsg >>
                                                                     ELSE /\ IF recoveredElem'[self] = "installer"
                                                                                THEN /\ installerInStartingMode(self[2])
                                                                                     /\ Assert(switchStatus[self[2]].cpu = NotFailed /\ switchStatus[self[2]].installer = Failed, 
                                                                                               "Failure of assertion at line 263, column 9 of macro called at line 599, column 52.")
                                                                                     /\ switchStatus' = [switchStatus EXCEPT ![self[2]].installer = NotFailed]
                                                                                     /\ IF switchStatus'[self[2]].nicAsic = NotFailed /\ switchStatus'[self[2]].ofa = NotFailed
                                                                                           THEN /\ Assert(switchStatus'[self[2]].installer = NotFailed, 
                                                                                                          "Failure of assertion at line 266, column 13 of macro called at line 599, column 52.")
                                                                                                /\ controlMsgCounter' = [controlMsgCounter EXCEPT ![self[2]] = controlMsgCounter[self[2]] + 1]
                                                                                                /\ statusResolveMsg' = [statusResolveMsg EXCEPT ![self] =                     [
                                                                                                                                                              type |-> KEEP_ALIVE,
                                                                                                                                                              swID |-> self[2],
                                                                                                                                                              num |-> controlMsgCounter'[self[2]],
                                                                                                                                                              installerStatus |-> getInstallerStatus(switchStatus'[self[2]].installer)
                                                                                                                                                          ]]
                                                                                                /\ switch2Controller' = Append(switch2Controller, statusResolveMsg'[self])
                                                                                           ELSE /\ TRUE
                                                                                                /\ UNCHANGED << switch2Controller, 
                                                                                                                controlMsgCounter, 
                                                                                                                statusResolveMsg >>
                                                                                ELSE /\ Assert(FALSE, 
                                                                                               "Failure of assertion at line 600, column 18.")
                                                                                     /\ UNCHANGED << switch2Controller, 
                                                                                                     switchStatus, 
                                                                                                     controlMsgCounter, 
                                                                                                     statusResolveMsg >>
                                                               /\ UNCHANGED controller2Switch
                                                    /\ UNCHANGED << NicAsic2OfaBuff, 
                                                                    Ofa2NicAsicBuff, 
                                                                    Installer2OfaBuff, 
                                                                    Ofa2InstallerBuff >>
                                         /\ TCAM' = TCAM
                              /\ RecoveryStatus' = [RecoveryStatus EXCEPT ![self[2]] = [transient |-> 0, partial |-> 0]]
                              /\ pc' = [pc EXCEPT ![self] = "SwitchResolveFailure"]
                              /\ UNCHANGED << switchLock, controllerLock, 
                                              sw_fail_ordering_var, 
                                              installedIRs, ingressPkt, 
                                              ingressIR, egressMsg, ofaInMsg, 
                                              ofaOutConfirmation, 
                                              installerInIR, statusMsg, 
                                              notFailedSet, failedElem, obj >>

swResolveFailure(self) == SwitchResolveFailure(self)

ghostProc(self) == /\ pc[self] = "ghostProc"
                   /\ /\ switchLock # <<NO_LOCK, NO_LOCK>>
                      /\ switchLock[2] = self[2]
                      /\ controllerLock = <<NO_LOCK, NO_LOCK>>
                   /\ IF WHICH_SWITCH_MODEL[self[2]] = SW_SIMPLE_MODEL
                         THEN /\ switchStatus[switchLock[2]].nicAsic = Failed
                         ELSE /\ IF switchStatus[switchLock[2]].cpu = Failed /\ switchLock[1] = NIC_ASIC_OUT
                                    THEN /\ pc[switchLock] = "SwitchFromOFAPacket"
                                    ELSE /\ IF switchLock[1] \in {NIC_ASIC_IN, NIC_ASIC_OUT}
                                               THEN /\ switchStatus[switchLock[2]].nicAsic = Failed
                                                    /\ /\ pc[<<NIC_ASIC_IN, self[2]>>] = "SwitchRcvPacket"
                                                       /\ pc[<<NIC_ASIC_OUT, self[2]>>] = "SwitchFromOFAPacket"
                                               ELSE /\ IF switchLock[1] \in {OFA_IN, OFA_OUT}
                                                          THEN /\ switchStatus[switchLock[2]].ofa = Failed
                                                               /\ /\ pc[<<OFA_IN, self[2]>>] = "SwitchOfaProcIn"
                                                                  /\ pc[<<OFA_OUT, self[2]>>] = "SwitchOfaProcOut"
                                                          ELSE /\ IF switchLock[1] \in {INSTALLER}
                                                                     THEN /\ switchStatus[switchLock[2]].installer = Failed
                                                                          /\ pc[<<INSTALLER, self[2]>>] = "SwitchInstallerProc"
                                                                     ELSE /\ TRUE
                   /\ Assert(\/ switchLock[2] = switchLock[2]
                             \/ switchLock[2] = NO_LOCK, 
                             "Failure of assertion at line 361, column 9 of macro called at line 636, column 9.")
                   /\ switchLock' = <<NO_LOCK, NO_LOCK>>
                   /\ pc' = [pc EXCEPT ![self] = "ghostProc"]
                   /\ UNCHANGED << controllerLock, sw_fail_ordering_var, 
                                   controller2Switch, switch2Controller, 
                                   switchStatus, installedIRs, NicAsic2OfaBuff, 
                                   Ofa2NicAsicBuff, Installer2OfaBuff, 
                                   Ofa2InstallerBuff, TCAM, controlMsgCounter, 
                                   RecoveryStatus, ingressPkt, ingressIR, 
                                   egressMsg, ofaInMsg, ofaOutConfirmation, 
                                   installerInIR, statusMsg, notFailedSet, 
                                   failedElem, obj, failedSet, 
                                   statusResolveMsg, recoveredElem >>

ghostUnlockProcess(self) == ghostProc(self)

Next == (\E self \in ({SW_SIMPLE_ID} \X SW): swProcess(self))
           \/ (\E self \in ({NIC_ASIC_IN} \X SW): swNicAsicProcPacketIn(self))
           \/ (\E self \in ({NIC_ASIC_OUT} \X SW): swNicAsicProcPacketOut(self))
           \/ (\E self \in ({OFA_IN} \X SW): ofaModuleProcPacketIn(self))
           \/ (\E self \in ({OFA_OUT} \X SW): ofaModuleProcPacketOut(self))
           \/ (\E self \in ({INSTALLER} \X SW): installerModuleProc(self))
           \/ (\E self \in ({SW_FAILURE_PROC} \X SW): swFailureProc(self))
           \/ (\E self \in ({SW_RESOLVE_PROC} \X SW): swResolveFailure(self))
           \/ (\E self \in ({GHOST_UNLOCK_PROC} \X SW): ghostUnlockProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_vars(swProcess(self))
        /\ \A self \in ({NIC_ASIC_IN} \X SW) : WF_vars(swNicAsicProcPacketIn(self))
        /\ \A self \in ({NIC_ASIC_OUT} \X SW) : WF_vars(swNicAsicProcPacketOut(self))
        /\ \A self \in ({OFA_IN} \X SW) : WF_vars(ofaModuleProcPacketIn(self))
        /\ \A self \in ({OFA_OUT} \X SW) : WF_vars(ofaModuleProcPacketOut(self))
        /\ \A self \in ({INSTALLER} \X SW) : WF_vars(installerModuleProc(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_vars(swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_vars(swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_vars(ghostUnlockProcess(self))

\* END TRANSLATION 
=============================================================================
