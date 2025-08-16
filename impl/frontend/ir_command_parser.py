from nib.nib_defs import IR, IR_TYPE, OFC_ROLE
from openflow.ofc_defs import get_gen_id
import openflow.ryulib.openflow_v13_parser as maker
import openflow.ryulib.openflow_v13_defs as defs


class IRCommandParser:
        # NOTE: Removed SEND_FLOW_REM flag, we don't need it anymore ...
        DEF_KEYS_INSTALL = {
                'table_id': 0,
                'priority': defs.OFP_DEFAULT_PRIORITY,
                'idle_timeout': 0,
                'hard_timeout': 0
                # 'flags': defs.OFPFF_SEND_FLOW_REM
        }

        DEF_KEYS_DELETE = {
                'table_id': 0
        }

        DEF_KEYS_STATS = {
                'table_id': 0
        }

        @classmethod
        def parse(cls, ir: IR):
                if ir.type == IR_TYPE.INSTALL_FLOW:
                        match, instructions, cookie, keys = IRCommandParser._parse_install_flow(ir)
                        return cls.get_install_flow(match, instructions, keys, cookie=cookie)
                elif ir.type == IR_TYPE.DELETE_FLOW:
                        match, keys, cookie = IRCommandParser._parse_delete_flow(ir)
                        return cls.get_delete_flow(match, keys, cookie)
                elif ir.type in {IR_TYPE.FLOW_STAT_REQ, IR_TYPE.PERIODIC_REQ}:
                        return cls.get_flow_stats()
                elif ir.type == IR_TYPE.INSTALL_GROUP:
                        group_id, group_type, buckets = cls._parse_install_group(ir)
                        return cls.get_install_group(group_id, group_type, buckets)
                elif ir.type == IR_TYPE.DELETE_GROUP:
                        group_id = cls._parse_delete_group(ir)
                        return cls.get_delete_group(group_id)
                elif ir.type in {IR_TYPE.GROUP_STAT_REQ, IR_TYPE.PERIODIC_GROUP_REQ}:
                        return cls.get_group_desc_stats()
                elif ir.type == IR_TYPE.ROLE_REQ:
                        role = cls._parse_role_req(ir)
                        return cls.get_role_req(role)
                raise ValueError(f"Unrecognized type {ir.type}")

        @classmethod
        def _parse_install_flow(cls, ir: IR):
                ir_cookie = ir.cookie
                ir_command = ir.command
                ir_command_no_space = ir_command.replace(' ', '')
                match_and_action = ir_command_no_space.split(",actions=")
                if len(match_and_action) != 2:
                        raise ValueError(f"Could not parse the given command {ir_command}")
                match = match_and_action[0]
                action = match_and_action[1]

                match_fields = match.split(',')
                action_fields = action.split(',')

                match, other_keys = cls._get_match(match_fields)
                instruction = cls._get_instruction(action_fields)

                return match, instruction, ir_cookie, other_keys

        @classmethod
        def _parse_delete_flow(cls, ir: IR):
                # DELETE_FLOW cookies are atually for their target, not themselves
                ir_cookie = ir.cookie
                ir_command = ir.command
                ir_command_no_space = ir_command.replace(' ', '')

                match_and_action = ir_command_no_space.split(",actions=")
                ir_command_no_space = match_and_action[0]

                if len(ir_command_no_space) > 0:
                        match_fields = ir_command_no_space.split(',')
                        match, other_keys = cls._get_match(match_fields)
                else:
                        match = None
                        other_keys = {}

                return match, other_keys, ir_cookie

        @classmethod
        def _parse_install_group(cls, ir: IR):
                rest_and_buckets = ir.command.replace(' ', '').split(',bucket=')
                if len(rest_and_buckets) < 2:
                        raise ValueError(f"Could not parse the given Install Group command: {ir.command}")

                key_vals = rest_and_buckets[0].split(',')
                buckets = rest_and_buckets[1:]

                group_id = None
                group_type = None
                for key_val in key_vals:
                        key, val = key_val.split('=')
                        if key == 'group_id':
                                group_id = int(val)
                        elif key == 'type':
                                group_type = cls.__get_group_type(val)

                if group_id is None or group_type is None:
                        raise ValueError(f"Group ID or Group Type unspecified in command: {ir.command}")

                buckets = [cls._get_bucket(action_fields) for action_fields in buckets]

                return group_id, group_type, buckets

        @staticmethod
        def __get_group_type(type_str):
                if type_str == 'all':
                        return defs.OFPGT_ALL
                elif type_str == 'select':
                        return defs.OFPGT_SELECT
                elif type_str == 'indirect':
                        return defs.OFPGT_INDIRECT
                elif type_str == 'ff':
                        return defs.OFPGT_FF

        @classmethod
        def _parse_delete_group(cls, ir: IR):
                fields = ir.command.replace(' ', '').split(',')
                group_id = None
                for field in fields:
                        if 'group_id' in field:
                                group_id = int(field.split('=')[1])

                if group_id is None:
                        raise ValueError(f"Group ID not specified in delete group command: {ir.command}")

                return group_id

        @classmethod
        def _parse_role_req(cls, ir: IR):
                try:
                        return OFC_ROLE[ir.command]
                except KeyError:
                        raise ValueError(f"Undefined role {ir.command}")

        @classmethod
        def get_install_flow(cls, match: maker.OFPMatch, instructions, keys,
                                                 send_flow_rem=True, cookie=0):
                kwargs = cls.DEF_KEYS_INSTALL.copy()
                for key, value in keys.items():
                        kwargs[key] = value
                if not send_flow_rem:
                        kwargs.pop('flags')

                return maker.OFPFlowMod(None, match=match, instructions=instructions, cookie=cookie, **kwargs)

        @classmethod
        def get_delete_flow(cls, match: maker.OFPMatch, keys, cookie):
                kwargs = cls.DEF_KEYS_DELETE.copy()
                for key, value in keys.items():
                        kwargs[key] = value

                return maker.OFPFlowMod(None, command=defs.OFPFC_DELETE, match=match, cookie=cookie,
                                                                cookie_mask=0xffffffffffffffff, out_port=defs.OFPP_ANY, out_group=defs.OFPG_ANY,
                                                                **kwargs)

        @classmethod
        def get_clear_table(cls, table_id):
                return maker.OFPFlowMod(None, command=defs.OFPFC_DELETE, table_id=table_id)

        @staticmethod
        def get_flow_stats():
                return maker.OFPFlowStatsRequest(None)

        @staticmethod
        def get_group_desc_stats():
                return maker.OFPGroupDescStatsRequest(None)

        @classmethod
        def get_install_group(cls, group_id, group_type, buckets):
                return maker.OFPGroupMod(
                        datapath=None,
                        type_=group_type,
                        buckets=buckets,
                        group_id=group_id,
                )

        @classmethod
        def get_delete_group(cls, group_id):
                return maker.OFPGroupMod(
                        datapath=None,
                        command=defs.OFPGC_DELETE,
                        group_id=group_id
                )

        @classmethod
        def get_role_req(cls, role):
                return maker.OFPRoleRequest(
                        datapath=None,
                        role=role.value,
                        generation_id=get_gen_id()
                )

        @classmethod
        def _get_match(cls, match_fields):
                match_keys = {}
                other_keys = {}
                for key_val in match_fields:
                        key_val_split = key_val.split('=')
                        if len(key_val_split) != 2:
                                if key_val == 'ip' or key_val == 'icmp':
                                        match_keys['eth_type'] = 0x800
                                elif key_val == 'arp':
                                        match_keys['eth_type'] = 0x806
                                else:
                                        raise ValueError(f"Could not parse match field and value {key_val}")
                                continue

                        if key_val_split[0] == 'table' or key_val_split[0] == 'table_id':
                                other_keys['table_id'] = int(key_val_split[1])
                        elif key_val_split[0] == 'priority':
                                other_keys['priority'] = int(key_val_split[1])
                        elif key_val_split[0] == 'nw_dst':
                                match_keys['ipv4_dst'] = key_val_split[1]
                        elif key_val_split[0] == 'nw_src':
                                match_keys['ipv4_src'] = key_val_split[1]
                        else:
                                try:
                                        match_keys[key_val_split[0]] = int(key_val_split[1], 0)
                                except ValueError:
                                        match_keys[key_val_split[0]] = key_val_split[1]

                return maker.OFPMatch(**match_keys), other_keys

        @classmethod
        def _get_action_list(cls, action_fields):
                actions = []
                for action_field in action_fields:
                        action_field_split = action_field.split(':', 1)
                        if len(action_field_split) != 2:
                                raise ValueError(f"Could not parse action field and value {action_field}")

                        if action_field_split[0] == 'output':
                                if action_field_split[1] == 'CONTROLLER':
                                        actions.append(maker.OFPActionOutput(port=defs.OFPP_CONTROLLER))
                                else:
                                        actions.append(maker.OFPActionOutput(port=int(action_field_split[1])))
                        elif action_field_split[0] == 'mod_dl_dst':
                                actions.append(maker.OFPActionSetField(eth_dst=action_field_split[1]))
                        elif action_field_split[0] == 'group':
                                actions.append(maker.OFPActionGroup(group_id=int(action_field_split[1])))
                        else:
                                raise NotImplementedError(f"Not yet implemented for action {action_field_split[0]}")

                return actions

        @classmethod
        def _get_group_action_list(cls, action_fields):
                actions = []
                properties = {}

                for action_field in action_fields:
                        if ':' in action_field:
                                action_field_split = action_field.split(':', 1)
                                if len(action_field_split) != 2:
                                        raise ValueError(f"Could not parse action field and value {action_field}")

                                if action_field_split[0] == 'output':
                                        if action_field_split[1] == 'CONTROLLER':
                                                actions.append(maker.OFPActionOutput(port=defs.OFPP_CONTROLLER))
                                        else:
                                                actions.append(maker.OFPActionOutput(port=int(action_field_split[1])))
                                else:
                                        raise NotImplementedError(f"Not yet implemented for action {action_field_split[0]}")
                        elif '=' in action_field:
                                property_field_split = action_field.split('=', 1)
                                if len(property_field_split) != 2:
                                        raise ValueError(f"Could not parse group action property field and value {action_field}")

                                if property_field_split[0] == 'weight':
                                        try:
                                                weight = int(property_field_split[1])
                                                properties['weight'] = weight
                                        except ValueError:
                                                properties['weight'] = 1
                                else:
                                        raise NotImplementedError(f"Note yet implemented for group action property \'{property_field_split[1]}\'")
                        else:
                                raise ValueError(f"Could not parse action field \'{action_field}\'")

                # At the very least, weight needs to be specified
                if 'weight' not in properties:
                        properties['weight'] = 1

                return actions, properties

        @classmethod
        def _get_instruction(cls, action_fields):
                if type(action_fields) == str:
                        action_fields = action_fields.split(',')

                actions = cls._get_action_list(action_fields)
                return [maker.OFPInstructionActions(defs.OFPIT_APPLY_ACTIONS, actions)]

        @classmethod
        def _get_bucket(cls, action_fields):
                if type(action_fields) == str:
                        action_fields = action_fields.split(',')

                actions, properties = cls._get_group_action_list(action_fields)
                return maker.OFPBucket(actions=actions, **properties)


if __name__ == '__main__':
        ir = IR(
                command="table=0,in_port=1,eth_type=0x0806,arp_tpa=10.0.0.2,actions=mod_dl_dst:4a:72:14:4a:c9:25,output:3",
                dp_id=1,
                cookie=3
        )

        res = IRCommandParser.parse(ir)
        print(f"Inst: {res.instructions}")
        print(f"Match: {res.match}")

        ir = IR(
                command="group_id=1,type=select,bucket=output:1,weight=10,bucket=weight=3,output:2",
                dp_id=1,
                cookie=1,
                type=IR_TYPE.INSTALL_GROUP
        )

        res = IRCommandParser.parse(ir)
        print(f"GID: {res.group_id}")
        print(f"TYPE: {res.type}")
        print("BUCKETS:")
        for bucket in res.buckets:
                print(f"\tWeight={bucket.weight} --- {bucket.actions}")

        ir = IR(
                command="table_id=0,priority=10,ip,actions=group:1",
                dp_id=1,
                cookie=10
        )

        res = IRCommandParser.parse(ir)
        print(f"Inst: {res.instructions}")
        print(f"Match: {res.match}")

        from nib.nib_events import QueuedIR

        ir = IR(
                command=str(OFC_ROLE.ROLE_SLAVE), dp_id=2, type=IR_TYPE.ROLE_REQ
        )

        queued_ir = QueuedIR(ir, -1)

        res = IRCommandParser.parse(queued_ir.ir)
        print(res)
        res.serialize()
        print(res.buf)