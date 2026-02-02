"""
# Anthropic's Original Performance Engineering Take-home (Release version)

Copyright Anthropic PBC 2026. Permission is granted to modify and use, but not
to publish or redistribute your solutions so it's hard to find spoilers.

# Task

- Optimize the kernel (in KernelBuilder.build_kernel) as much as possible in the
  available time, as measured by test_kernel_cycles on a frozen separate copy
  of the simulator.

We recommend you look through problem.py next.
"""

from collections import defaultdict
from dataclasses import dataclass
import random
import unittest

from problem import (
    Engine,
    DebugInfo,
    SLOT_LIMITS,
    VLEN,
    N_CORES,
    SCRATCH_SIZE,
    Machine,
    Tree,
    Input,
    HASH_STAGES,
    reference_kernel,
    build_mem_image,
    reference_kernel2,
)

@dataclass
class MultiSlot:
    slots: List[tuple]

class Buffer:
    e: str
    slots: List[tuple]

    def __init__(self):
        self.e = None
        self.slots = []

    def push(self, inst) -> bool:
        # print(f'pushing {inst}')
        if self.e == None:
            self.e = inst[0]
            self.slots = [s for s in inst[1]]
            return True
        if inst[0] == self.e:
            self.slots.extend(inst[1])
            return True
        return False

    def top(self):
        return self.slots[0]

    def pop(self):
        if len(self.slots) == 0:
            return None
        s = self.slots[0]
        self.slots = self.slots[1:]
        if len(self.slots) == 0:
            e = None
        return s

    def empty(self) -> bool:
        return len(self.slots) == 0

def areas_overlap(a1, l1, a2, l2):
    overlap, adjacent = True, False
    if a1+l1 <= a2:
        overlap = False
    if a2+l2 <= a1:
        overlap = False
    adjacent = a1+l1 == a2 or a2+l2 == a1
    return overlap, adjacent

def areas_adjacent(a1, l1, a2, l2):
    return a1+l1 == a2 or a2+l2 == a1

def mergeable(a1, l1, a2, l2):
    overlap, _ = areas_overlap(a1, l1, a2, l2)
    return areas_adjacent(a1, l1, a2, l2) or overlap

def addresses(slot):
    return slot[1:] if slot[0] != 'load_offset' else slot[1:-1]

class Scratch():
    scratch: List[tuple]
    def __init__(self):
        self.scratch = []

    def area_overlap(self, a1, l1) -> bool:
        for a2, l2 in self.scratch:
            o, _ = areas_overlap(a1, l1, a2, l2)
            if o:
                return True
        return False

    def insert(self, a1, l1):
        for a2, l2 in self.scratch:
            if mergeable(a1, l1, a2, l2):
                found = True
                self.scratch.remove((a2, l2))
                self.scratch.append((min(a1, a2),max(a2+l2,a1+l1)-min(a1, a2)))
                return
        self.scratch.append((a1, l1))

    def __str__(self):
        return f'{self.scratch}'

    def __repr__(self):
        return f'{self.scratch}'

class OptimizedInstruction():
    e: str
    slots: tuple
    written_scratch: Scratch
    read_scratch: Scratch

    def __init__(self, e):
        self.e = e
        self.slots = []
        self.written_scratch = Scratch()
        self.read_scratch = Scratch()

    def inst_length(self, e, op):
        if e in ['alu', 'debug']:
            return 1
        if e in ['valu']:
            return 8

        if e in ['store', 'load']:
            if op in ['vload', 'vstore']:
                return 8
            if op in ['store', 'load', 'load_offset', 'const']:
                return 1
            assert False, f'unknown op {e} {op}'
        assert False, f'unknown e {e}'
        lengths = {
            'alu' : 1,
            'valu' : 8,
            'load' : 1,
            'vload' : 8,
            'debug': 1,
            'store': 1,
            'vstore':8
            }
        return lengths[e]

    def slot_overlaps(self, e, slot):
        offset = 0 if slot[0] != 'load_offset' else slot[3]
        length = self.inst_length(e, slot[0])
        waddr = slot[1] + offset

        overlap = False
        if self.written_scratch.area_overlap(waddr, length):
            overlap = True

        if self.read_scratch.area_overlap(waddr, length):
            overlap = True

        read_addrs = slot[2:] if slot[0] != 'load_offset' else slot[2:-1]
        for raddr in read_addrs:
            raddr += offset
            if self.written_scratch.area_overlap(raddr, length):
                overlap = True

        return overlap

    def permitted(self, e, slot) -> bool:
        permitted = True
        if self.full():
        # if len(self.slots) == 2:
            permitted = False

        if self.e != e:
            permitted = False
        if self.slot_overlaps(e, slot):
            permitted = False
        return permitted

    def insert_area(self, e, slot):
        offset = 0 if slot[0] != 'load_offset' else slot[3]
        length = self.inst_length(e, slot[0])
        taddr = slot[1] + offset

        self.written_scratch.insert(taddr, length)
        read_addrs = slot[2:] if slot[0] != 'load_offset' else slot[2:-1]
        for raddr in read_addrs:
            raddr += offset
            self.read_scratch.insert(raddr, length)
      

    def add_and_register(self, e, slot) -> bool:
        if not ENABLED:
            self.slots.append(slot)
            return
        assert self.permitted(e, slot), f'Trying to add an unpermitted instruction'
        self.slots.append(slot)
        self.register(e, slot)

     

    def register(self, e, slot):
        # print(f'register {e=} {slot=}')
        if len(self.slots) <= SLOT_LIMITS[self.e]:
            self.insert_area(e, slot)

    def full(self) -> bool:
        return len(self.slots) == SLOT_LIMITS[self.e]

    def build(self):
        return {self.e: self.slots}

    
ENABLED = True

class Compiler:
    def __init__(self, insts, debug = False):
        self.input = insts
        self.curr = {}
        self.curr['valu'] = []
        self.curr['load'] = []
        self.curr['alu'] = []
        self.output = []
        self.debug = debug

    def flush(self, force: bool):
        for e, v in self.curr:
            assert len(v) <= SLOT_LIMITS[e], f'too much slots in curr[{e}]'
            if len(v) == SLOT_LIMITS[e] or force:
                self.output.append({e: self.curr[e]})

    def optimize(self, e, slot):
        if not ENABLED:
            return False, len(self.optimized)

        if self.debug:
            print(f'optimizing {slot}')
        found = False
        # iterate optimized, and find a non-coliding spot
        seen = [0]
        for a in addresses(slot):
            if a in self.last_seen:
                seen.append(self.last_seen[a])
        i = max(seen)
        while i < len(self.optimized) and not found:
            opz = self.optimized[i]
            if opz.permitted(e, slot):
                opz.add_and_register(e, slot)
                found = True
                break
            if e == 'load' and opz.e in ['valu', 'alu']:
                if not opz.slot_overlaps(e, slot):
                    nopz = OptimizedInstruction(e)
                    nopz.add_and_register(e, slot)
                    self.optimized = self.optimized[:i] + [nopz] + self.optimized[i:]
                    found = True
                    for addr in self.last_seen:
                        if self.last_seen[addr] >= i:
                            self.last_seen[addr] = self.last_seen[addr]+1
                    break

            opz.register(e, slot)
            
            i += 1
        return found, i

    def compile(self):
        stock = [self.decompose(i) for i in self.input]
        buffer = []
        if self.debug:
            print('\n'.join([f'{i}' for i in stock]))
        # stock.reverse()

        self.optimized = []
        self.last_seen = {}
        for s in stock:
            e = s[0]
            for slot in s[1]:
                # if self.debug:
                #     for opz in self.optimized:
                #         print(f'{opz.e=} {opz.slots=}')
                #         print(f'\t{opz.read_scratch=}')
                #         print(f'\t{opz.written_scratch=}')
                #     print('==================')
                # if self.debug:
                #     print(f'optimizing {slot}')
                # found = False
                # # iterate optimized, and find a non-coliding spot
                # seen = [0]
                # for a in addresses(slot):
                #     if a in last_seen:
                #         seen.append(last_seen[a])
                # i = max(seen)
                # while i < len(self.optimized) and not found:
                #     opz = self.optimized[i]
                #     if opz.permitted(e, slot):
                #         opz.add_and_register(e, slot)
                #         found = True
                #         break
                #     if e == 'load' and opz.e in ['valu', 'alu']:
                #         if not opz.slot_overlaps(e, slot):
                #             nopz = OptimizedInstruction(e)
                #             nopz.add_and_register(e, slot)
                #             self.optimized = self.optimized[:i] + [nopz] + self.optimized[i:]
                #             found = True
                #             for addr in last_seen:
                #                 if last_seen[addr] >= i:
                #                     last_seen[addr] = last_seen[addr]+1
                #             break

                #     opz.register(slot)
                    
                #     i += 1
                found, i = self.optimize(e, slot)
                if not found:
                    opz = OptimizedInstruction(e)
                    opz.add_and_register(e, slot)
                    self.optimized.append(opz)
                # update last_seen
                addr = slot[1]
                self.last_seen[addr] = i
                # for addr in addresses(slot):
                #     last_seen[addr] = i

        if self.debug:
            for opz in self.optimized:
                print(f'{opz.e=} {opz.slots=}')
                print(f'\t{opz.read_scratch=}')
                print(f'\t{opz.written_scratch=}')
        self.output.extend([opz.build() for opz in self.optimized])

        if self.debug:
            print('done compiling')
            print('\n'.join([f'{len([i[k] for k in i][0])}: {i}' for i in self.output]))


                
    def decompose(self, inst) -> (Engine, List[tuple]):
        e, slot = inst
        slots = []
        if isinstance(slot, MultiSlot):
            slots.extend(slot.slots)
        elif isinstance(slot, tuple):
            slots.append(slot)
        return e, slots

    def build(self) -> list[dict[Engine, tuple]]:
        # self.flush(True)
        # return self.output
        return self.output

class KernelBuilder:
    def __init__(self):
        self.instrs = []
        self.scratch = {}
        self.scratch_debug = {}
        self.scratch_ptr = 0
        self.const_map = {}

    def debug_info(self):
        return DebugInfo(scratch_map=self.scratch_debug)

    def build(self, slots: list[tuple[Engine, tuple]], vliw: bool = False):
        # Simple slot packing that just uses one slot per instruction bundle
        instrs = []
        for engine, slot in slots:
            instrs.append({engine: [slot]})
        return instrs

    def build_multi(self, slots: list[tuple[Engine, any]], vliw: bool = False):
        instrs = []
        for engine, slot in slots:
            if isinstance(slot, MultiSlot):
                instrs.append({engine: slot.slots})
            elif isinstance(slot, tuple):
                instrs.append({engine: [slot]})
            else:
                raise Exception(f"Unrecognised type {type(slot)}")
        return instrs

    

    def combine_insts(self, insts: list[dict[Engine, tuple]]):
        engines = [k for k,_ in insts]
        assert len(set(engines)) == 1, f'strange engine type set {set(engines)=}'
        e = engines[0]

        slots = []
        for _, slot in insts:
            if isinstance(slot, MultiSlot):
                slots.extend(slot.slots)
            elif isinstance(slot, tuple):
                slots.append(slot)
            else:
                raise Exception('unrecognized type')

        combined = []
        assert len(slots) == len(set([s[1] for s in slots])), f'slots: {slots=}'
        while len(slots) > 0:

            limit = SLOT_LIMITS[e]
            # assert len(slots) % limit == 0, f'{insts=}'
            combined.append({e: slots[:limit]})
            slots = slots[limit:]
        return combined

    def build_compress(self, body: list, batch_size: int, rounds: int):
        assert len(body) % (batch_size/VLEN) == 0
        iter_length = int(len(body) / (batch_size/VLEN))

        round_length = int(iter_length / rounds)

        batches = int(len(body)/round_length)
        # print(f'{len(body)=} {round_length=} {batches=}')

        # combine every mb_size iterations
        # mb_size = self.mb_size
        insts = []
        while batches > 0:
            mb_size = int(min(self.mb_size, batches))
            # print(f'{batches=} {mb_size=}')
            # stories = [body[i*iter_length:(i+1)*iter_length] for i in range(mb_size)]
            stories = [body[i*round_length:(i+1)*round_length] for i in range(mb_size)]


            assert all([len(s) == round_length for s in stories]), f'lengths={[len(s) for s in stories]}'
            
            for i in range(round_length):
                uncombined = [s[i] for s in stories]
                combined = self.combine_insts(uncombined)
                insts.extend(combined)
            body = body[mb_size * round_length:]
            batches -= mb_size
            # print(f'{len(insts)=}')
        return insts

    def compile(self, insts, debug = False):
        compiler = Compiler(insts, debug = debug)
        compiler.compile()
        return compiler.build()
            

    def build_optimize(self, body: list, batch_size: int, rounds: int):
        effected = []
        read = []

        assert all([e in ['valu', 'load', 'alu'] for e in body]), f'body has an instruction not in [valu, load, alu]'
        curr_valu = []
        curr_load = []

        for inst in body:
            e, slots = self.get_slots(inst)




    def add(self, engine, slot):
        self.instrs.append({engine: [slot]})

    def alloc_scratch(self, name=None, length=1):
        addr = self.scratch_ptr
        assert name not in self.scratch, f'name {name} already exists in scratch memory'
        if name is not None:
            self.scratch[name] = addr
            # print(f'adding {name=} to the debug scratchmap')
            self.scratch_debug[addr] = (name, length)
        self.scratch_ptr += length
        assert self.scratch_ptr <= SCRATCH_SIZE, f'Out of scratch space when trying to allocate {name}'
        return addr

    def scratch_const(self, val, name=None):
        if val not in self.const_map:
            addr = self.alloc_scratch(name)
            self.add("load", ("const", addr, val))
            self.const_map[val] = addr
        return self.const_map[val]

    def build_hash(self, val_hash_addr, tmp1, tmp2, round, i):
        slots = []

        for hi, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            slots.append(("alu", MultiSlot(slots=((op1, tmp1, val_hash_addr, self.scratch_const(val1)),(op3, tmp2, val_hash_addr, self.scratch_const(val3))))))
            slots.append(("alu", (op2, val_hash_addr, tmp1, tmp2)))

        return slots

    def init_hash(self):
        self.hash_consts = {}
        self.hash_factor = {}
        slots = []
        for hi, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            const1 = self.alloc_scratch(f'hash_val1_{hi}', VLEN)
            slots.append(("valu", ("vbroadcast", const1, self.scratch_const(val1))))

            if hi in [0,2,4]:
                const3 = self.alloc_scratch(f'hash_vfconst_{hi}', VLEN)
                slots.append(("valu", ("vbroadcast", const3, self.scratch_const(1<<val3))))
            else:
                const3 = self.alloc_scratch(f'hash_val3_{hi}', VLEN)
                slots.append(("valu", ("vbroadcast", const3, self.scratch_const(val3))))

            self.hash_consts[hi] = (const1, const3)
        return slots

    def build_vhash(self, val_hash_addr_v, vtmp1, vtmp2, round, i):
        slots = []
        # HASH_STAGES = [
        #     ("+", 0x7ED55D16, "+", "<<", 12),
        #     ("^", 0xC761C23C, "^", ">>", 19),
        #     ("+", 0x165667B1, "+", "<<", 5),
        #     ("+", 0xD3A2646C, "^", "<<", 9),
        #     ("+", 0xFD7046C5, "+", "<<", 3),
        #     ("^", 0xB55A4F09, "^", ">>", 16),
        # ]
        hi = 0
        const1, const3 = self.hash_consts[hi]
        op1, val1, op2, op3, val3 = HASH_STAGES[hi]
        slots.append(("valu", (op1, vtmp1, val_hash_addr_v, const1)))
        slots.append(("valu", ("multiply_add", val_hash_addr_v, val_hash_addr_v, const3, vtmp1)))
        hi = 1
        const1, const3 = self.hash_consts[hi]
        op1, val1, op2, op3, val3 = HASH_STAGES[hi]
        slots.append(("valu", (op1, vtmp1, val_hash_addr_v, const1)))
        slots.append(("valu", (op3, vtmp2, val_hash_addr_v, const3)))
        slots.append(("valu", (op2, val_hash_addr_v, vtmp1, vtmp2)))
        hi = 2
        const1, const3 = self.hash_consts[hi]
        op1, val1, op2, op3, val3 = HASH_STAGES[hi]
        slots.append(("valu", (op1, vtmp1, val_hash_addr_v, const1)))
        slots.append(("valu", ("multiply_add", val_hash_addr_v, val_hash_addr_v, const3, vtmp1)))
        hi = 3
        const1, const3 = self.hash_consts[hi]
        op1, val1, op2, op3, val3 = HASH_STAGES[hi]
        slots.append(("valu", (op1, vtmp1, val_hash_addr_v, const1)))
        slots.append(("valu", (op3, vtmp2, val_hash_addr_v, const3)))
        slots.append(("valu", (op2, val_hash_addr_v, vtmp1, vtmp2)))
        hi = 4
        const1, const3 = self.hash_consts[hi]
        op1, val1, op2, op3, val3 = HASH_STAGES[hi]
        slots.append(("valu", (op1, vtmp1, val_hash_addr_v, const1)))
        slots.append(("valu", ("multiply_add", val_hash_addr_v, val_hash_addr_v, const3, vtmp1)))
        hi = 5
        const1, const3 = self.hash_consts[hi]
        op1, val1, op2, op3, val3 = HASH_STAGES[hi]
        slots.append(("valu", (op1, vtmp1, val_hash_addr_v, const1)))
        slots.append(("valu", (op3, vtmp2, val_hash_addr_v, const3)))
        slots.append(("valu", (op2, val_hash_addr_v, vtmp1, vtmp2)))
        return slots

    def build_kernel(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        """
        Like reference_kernel2 but building actual instructions.
        Scalar implementation using only scalar ALU and load/store.
        """
        tmp1 = self.alloc_scratch("tmp1")
        # tmp2 = self.alloc_scratch("tmp2")
        # tmp3 = self.alloc_scratch("tmp3")
        # Scratch space addresses
        init_vars = [
            "rounds",
            "n_nodes",
            "batch_size",
            "forest_height",
            "forest_values_p",
            "inp_indices_p",
            "inp_values_p",
        ]
        for v in init_vars:
            self.alloc_scratch(v, 1)
        for i, v in enumerate(init_vars):
            self.add("load", ("const", tmp1, i))
            self.add("load", ("load", self.scratch[v], tmp1))

        zero_const = self.scratch_const(0)
        one_const = self.scratch_const(1)
        two_const = self.scratch_const(2)

        # Pause instructions are matched up with yield statements in the reference
        # kernel to let you debug at intermediate steps. The testing harness in this
        # file requires these match up to the reference kernel's yields, but the
        # submission harness ignores them.
        self.add("flow", ("pause",))
        # Any debug engine instruction is ignored by the submission simulator
        self.add("debug", ("comment", "Starting loop"))

        CONSTS = 5
        VCONSTS = 5
        const_int = [zero_const, one_const, two_const] + [self.scratch_const(i) for i in range(3,CONSTS)]
        vconst = [self.alloc_scratch(f'vconst{i}', VLEN) for i in range(VCONSTS)]
        body = []
        for i in range(VCONSTS):
            body.append(("valu", ("vbroadcast", vconst[i], const_int[i])))
        body_instrs = self.compile(body, False)
        self.instrs.extend(body_instrs)

        vone = vconst[1]
        vtwo = vconst[2]

        self.mb_size = 6
        vbatch_size = int(batch_size/VLEN)

        # Vector scratch registers
        # arr_vtmp1 = [self.alloc_scratch(f'vtmp1_{i}', VLEN) for i in range(32)]
        implemented_height = 6
        arr_vparity = []
        for x in range(self.mb_size):
            arr_vparity.append([self.alloc_scratch(f'vtmp1_{x}_{y}', VLEN) for y in range(implemented_height)])
        arr_vtmp2 = [self.alloc_scratch(f'vtmp2_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp3 = [self.alloc_scratch(f'vtmp3_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp4 = [self.alloc_scratch(f'vtmp4_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp5 = [self.alloc_scratch(f'vtmp5_{i}', VLEN) for i in range(self.mb_size)]

        arr_tmp_node_val_v  = [self.alloc_scratch(f'tmp_node_val_v_{i}', VLEN) for i in range(self.mb_size)]

        mega_idx_v = [self.alloc_scratch(f'mega_idx_v_{i}', VLEN) for i in range(vbatch_size)]
        mega_val_v = [self.alloc_scratch(f'mega_val_v_{i}', VLEN) for i in range(vbatch_size)]

        vforest_values_p = self.alloc_scratch('vforest_values_p', VLEN)


        body = []
        self.add("valu", ("vbroadcast", vforest_values_p, self.scratch['forest_values_p']))
        # The need to decrease here is because we are managing tmp_idx_v as 1-base instead of 0-base
        self.add("valu", ("-", vforest_values_p, vforest_values_p, vone))

        vtree = self.alloc_scratch('vtree', VLEN*4)
        ptr = arr_vtmp2[0]
        for i in range(4):
            body.append(("alu", ("<<", arr_vtmp2[i], const_int[i], const_int[3])))
            body.append(("alu", ("+", arr_vtmp2[i], arr_vtmp2[i], self.scratch['forest_values_p'])))
        for i in range(4):
            body.append(("load", ("vload", vtree+i*VLEN, arr_vtmp2[i])))

        NUM_STORED_VF = 2**5-1

        vforest_values = [self.alloc_scratch(f'vf{i}', VLEN) for i in range(NUM_STORED_VF)]
        for i in range(NUM_STORED_VF):
            body.append(("valu", ("vbroadcast", vforest_values[i], vtree+i)))

        vf = vforest_values
        
        for i in range(2, NUM_STORED_VF, 2):
            body.append(("valu", ("-", vforest_values[i], vforest_values[i], vforest_values[i-1])))

        body.extend(self.init_hash())
        body_instrs = self.compile(body, False)
        self.instrs.extend(body_instrs)

        assert batch_size % VLEN == 0

        body = []
        tmp_array = arr_vtmp2 + arr_vtmp3 + arr_vtmp4 + arr_vtmp5
        for i in range(0, batch_size, VLEN):
            vbatch = int(i/VLEN)
            mb_num = vbatch % self.mb_size

            vtmp2 = arr_vparity[0][0] + i

            tmp_idx_v = mega_idx_v[vbatch]
            tmp_val_v = mega_val_v[vbatch]


            # idx = mem[inp_indices_p + i]
            # val = mem[inp_values_p + i]
            # No need to initialize tmp_idx_v because it is zeros in the first place
            i_const = self.scratch_const(i)
            body.append(("alu", ("+", vtmp2, self.scratch["inp_values_p"], i_const)))
            body.append(("load",("vload", tmp_val_v, vtmp2)))

        body_instrs = self.compile(body)
        print(f'===== before: {len(body)} after:  {len(body_instrs)}')
        self.instrs.extend(body_instrs)
        # body_instrs = self.build_compress(body, batch_size, 1)
        # # body_instrs = self.compile(body)
        # self.instrs.extend(body_instrs)

        # tmp_node_val_v initiation method
        BROADCAST_ZERO = 0
        LOAD_ONE = 1
        LOAD_TWO = 2
        LOAD_THREE = 3
        LOAD_FOUR = 4

        NORMAL_LOAD = 999

        # idx iteration method
        WRAPAROUND = "wraparound"
        AFTER_WRAPAROUND = "after_wraparound"
        FIRST_NORMAL_ITERATE = "f"
        NORMAL_ITERATE = "normal_iterate"
        PARITY_AWARE = "parity_aware"
        FIRST_ITERATION = "first_iteration"

        STAGES_DICT = {
            0: [BROADCAST_ZERO, FIRST_ITERATION],
            1: [LOAD_ONE, PARITY_AWARE],
            2: [LOAD_TWO, PARITY_AWARE],
            3: [LOAD_THREE, PARITY_AWARE],
            4: [LOAD_FOUR, PARITY_AWARE],
            5: [NORMAL_LOAD, FIRST_NORMAL_ITERATE],
            #: [NORMAL_LOAD, NORMAL_ITERATE],
            10: [NORMAL_LOAD, WRAPAROUND],
            11: [BROADCAST_ZERO, AFTER_WRAPAROUND],
            12: [LOAD_ONE, AFTER_WRAPAROUND],
            13: [LOAD_TWO, AFTER_WRAPAROUND],
            14: [LOAD_THREE, AFTER_WRAPAROUND],
            15: [LOAD_FOUR, AFTER_WRAPAROUND],
        }

        # round_num = -1
        body = []  # array of slots
        for vbatch_i in range(0, batch_size, VLEN):
            for round in range(rounds):
                if round in STAGES_DICT:
                    load_method, iterate_method = STAGES_DICT[round]
                else:
                    load_method, iterate_method = NORMAL_LOAD, NORMAL_ITERATE

                vbatch = int(vbatch_i/VLEN)
                # print(f'{vbatch=} {round=}')
                mb_num = vbatch % self.mb_size
                # round_num += 1
                # mb_num = round_num % self.mb_size

                tlevel = round % (forest_height+1)
                vparity = arr_vparity[mb_num]
                vtmp1 = vparity[3]

                vtmp2 = arr_vtmp2[mb_num]
                vtmp3 = arr_vtmp3[mb_num]
                vtmp4 = arr_vtmp4[mb_num]
                vtmp5 = arr_vtmp5[mb_num]

                tmp_idx_v = mega_idx_v[vbatch]
                tmp_val_v = mega_val_v[vbatch]

                tmp_node_val_v = arr_tmp_node_val_v[mb_num]

                match load_method:
                    case x if x == BROADCAST_ZERO:
                        # using vf0 directly in "^" command
                        pass
                    case x if x == LOAD_ONE:
                        body.append(("valu", ("multiply_add", tmp_node_val_v, vparity[0], vf[2], vf[1])))
                    case x if x == LOAD_TWO:
                        body.append(("valu", MultiSlot(slots=(
                                ("multiply_add", tmp_node_val_v, vparity[1], vf[4], vf[3]),
                                ("multiply_add", vtmp2,          vparity[1], vf[6], vf[5]),
                            ))))

                        body.append(("valu", MultiSlot(slots=(
                                ("-", vtmp2, vtmp2, tmp_node_val_v),
                            ))))

                        body.append(("valu", ("multiply_add", tmp_node_val_v, vparity[0], vtmp2, tmp_node_val_v)))

                    case x if x == LOAD_THREE:
                        
                        tvector = [tmp_node_val_v, vtmp2, vtmp3, vtmp4]
                        base = 7
                        slots = []
                        for i in range(4):
                            slots.append(("multiply_add", tvector[i], vparity[2], vf[base+i*2+1], vf[base+i*2]))
                        body.append(("valu", MultiSlot(slots=slots)))

                        slots = []
                        for i in range(2):
                            slots.append(("-", tvector[i*2+1], tvector[i*2+1], tvector[i*2]))
                        body.append(("valu", MultiSlot(slots=slots)))

                        slots = []
                        for i in range(2):
                            slots.append(("multiply_add", tvector[i*2+1], vparity[1], tvector[i*2+1], tvector[i*2]))
                        body.append(("valu", MultiSlot(slots=slots)))

                        tvector = [vtmp2, vtmp4]
                        body.append(("valu", ("-", tvector[1], tvector[1], tvector[0])))
                        body.append(("valu", ("multiply_add", tmp_node_val_v, vparity[0], tvector[1], tvector[0])))

                    case x if x == LOAD_FOUR:
                        outputs = [tmp_node_val_v, vtmp2]
                        for offset in range(2):
                            base = 15+offset*8
                            tvector = [vtmp2, vtmp3, vtmp4, vtmp5]
                            slots = []

                            for i in range(4):
                                slots.append(("multiply_add", tvector[i], vparity[3], vf[base+i*2+1], vf[base+i*2]))
                            body.append(("valu", MultiSlot(slots=slots)))

                            slots = []
                            for i in range(2):
                                slots.append(("-", tvector[i*2+1], tvector[i*2+1], tvector[i*2]))
                            body.append(("valu", MultiSlot(slots=slots)))
                            slots = []
                            for i in range(2):
                                slots.append(("multiply_add", tvector[i*2+1], vparity[2], tvector[i*2+1], tvector[i*2]))
                            body.append(("valu", MultiSlot(slots=slots)))

                            tvector = [vtmp3, vtmp5]

                            body.append(("valu", ("-", tvector[1], tvector[1], tvector[0])))
                            body.append(("valu", ("multiply_add", outputs[offset], vparity[1], tvector[1], tvector[0])))
                            
                        tvector = [outputs[0], outputs[1]]
                        body.append(("valu", ("-", tvector[1], tvector[1], tvector[0])))
                        body.append(("valu", ("multiply_add", tmp_node_val_v, vparity[0], tvector[1], tvector[0])))
      
                    case x if x == NORMAL_LOAD:
                        if iterate_method == FIRST_NORMAL_ITERATE:
                            body.append(("valu", ("multiply_add", tmp_idx_v, vone,      vtwo, vparity[0])))
                            # body.append(("valu", ("multiply_add", vparity[1], vparity[1], vtwo, vparity[2])))
                            # body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vconst[4], vparity[1])))


                            body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[1])))
                            body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[2])))
                            body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[3])))
                            body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[4])))

                        body.append(("valu", ("+", vtmp2, tmp_idx_v, vforest_values_p)))
                        for j in range(VLEN):
                            # node_val = mem[forest_values_p + idx]
                            body.append(("load", ("load_offset", tmp_node_val_v, vtmp2, j)))


                # val = myhash(val ^ node_val)
                if load_method == BROADCAST_ZERO:
                    body.append(("valu", ("^", tmp_val_v, tmp_val_v, vf[0])))
                else:
                    body.append(("valu", ("^", tmp_val_v, tmp_val_v, tmp_node_val_v)))
                body.extend(self.build_vhash(tmp_val_v, vtmp3, vtmp2, round, i))
                self.add("debug", ("comment", "Vhash finished"))

                match iterate_method:
                    case x if x == FIRST_ITERATION:
                        body.append(("valu", ("%", vparity[tlevel], tmp_val_v, vtwo)))
                        # body.append(("valu", ("multiply_add", tmp_idx_v, vone, vtwo, vparity[tlevel])))
                    case x if x == FIRST_NORMAL_ITERATE:
                        # body.append(("valu", ("multiply_add", tmp_idx_v, vone,      vtwo, vparity[0])))
                        # body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[1])))
                        # body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[2])))
                        # body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[3])))
                        # body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[4])))

                        body.append(("valu", ("%", vtmp1, tmp_val_v, vtwo)))
                        body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vtmp1)))
                    case x if x == NORMAL_ITERATE:
                        body.append(("valu", ("%", vtmp1, tmp_val_v, vtwo)))
                        body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vtmp1)))
                    case x if x == PARITY_AWARE:
                        body.append(("valu", ("%", vparity[tlevel], tmp_val_v, vtwo)))
                        # body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vparity[tlevel])))
                    case x if x == WRAPAROUND:
                        # next iteration we just use vone instead of tmp_idx_v
                        pass
                    case x if x == AFTER_WRAPAROUND:
                        body.append(("valu", ("%", vparity[tlevel], tmp_val_v, vtwo)))

            # if mb_num == 5 or vbatch == 31:
            #     debug = False
            #     if vbatch == 11:
            #         debug = True
            #     # here we are compiling every vbatch on entire rounds
        debug = False
        body_instrs = self.compile(body, debug)
        print(f'===== before: {len(body)} after:  {len(body_instrs)}')
        self.instrs.extend(body_instrs)
        body = []


        body = []
        for i in range(0, batch_size, VLEN):
            vbatch = int(i/VLEN)
            mb_num = vbatch % self.mb_size

            vtmp3 = arr_vtmp3[mb_num]
            vtmp2 = arr_vtmp2[mb_num]

            tmp_idx_v = mega_idx_v[vbatch]
            tmp_val_v = mega_val_v[vbatch]

            # one last -1
            body.append(("valu", ("-", tmp_idx_v, tmp_idx_v, vone)))

            i_const = self.scratch_const(i)
            # mem[inp_indices_p + i] = idx
            # mem[inp_values_p + i] = val

            body.append(("alu", MultiSlot(slots=(("+", vtmp3, self.scratch["inp_indices_p"], i_const),
                                            ("+", vtmp2, self.scratch["inp_values_p"], i_const)))))
            body.append(("store", MultiSlot(slots=(("vstore", vtmp3, tmp_idx_v), 
                                            ("vstore", vtmp2, tmp_val_v)))))


        body_instrs = self.compile(body)
        print(f'===== before: {len(body)} after:  {len(body_instrs)}')
        self.instrs.extend(body_instrs)


        # Required to match with the yield in reference_kernel2
        self.instrs.append({"flow": [("pause",)]})

        used = 0
        total = 0
        gap = 0
        for i in self.instrs:
            # if i % 1000 == 0:
            #     print(total)
            for e, slots in i.items():
                if e == 'debug':
                    continue
                if len(slots) < SLOT_LIMITS[e] and e != 'debug':
                    # print(f'{e=} {slots=}, {len(slots)=} {SLOT_LIMITS[e]=}')
                    gap += SLOT_LIMITS[e] - len(slots)
                used  += len(slots)
                total += SLOT_LIMITS[e]
        print(f'efficiency: {used=} {total=} {gap=} ratio={1.0*used/total}')

        print(f'size of tree:{n_nodes}')

        print(f'scratch used: {self.scratch_ptr=} out of {SCRATCH_SIZE}')

BASELINE = 147734

def do_kernel_test(
    forest_height: int,
    rounds: int,
    batch_size: int,
    seed: int = 123,
    trace: bool = False,
    prints: bool = False,
):
    print(f"{forest_height=}, {rounds=}, {batch_size=}")
    random.seed(seed)
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)
    mem = build_mem_image(forest, inp)

    kb = KernelBuilder()
    kb.build_kernel(forest.height, len(forest.values), len(inp.indices), rounds)
    # print(kb.instrs)

    value_trace = {}
    machine = Machine(
        mem,
        kb.instrs,
        kb.debug_info(),
        n_cores=N_CORES,
        value_trace=value_trace,
        trace=trace,
    )
    machine.prints = prints
    for i, ref_mem in enumerate(reference_kernel2(mem, value_trace)):
        machine.run()
        inp_values_p = ref_mem[6]
        if prints:
            print(machine.mem[inp_values_p : inp_values_p + len(inp.values)])
            print(ref_mem[inp_values_p : inp_values_p + len(inp.values)])
        inp_indices_p = ref_mem[5]
        if prints:
            print(machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)])
            print(ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)])
        assert (
            machine.mem[inp_values_p : inp_values_p + len(inp.values)]
            == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
        ), f"Incorrect result on round {i}"
        
        # Updating these in memory isn't required, but you can enable this check for debugging
        # assert machine.mem[inp_indices_p:inp_indices_p+len(inp.indices)] == ref_mem[inp_indices_p:inp_indices_p+len(inp.indices)]

    print("CYCLES: ", machine.cycle)
    print("Speedup over baseline: ", BASELINE / machine.cycle)
    return machine.cycle


class Tests(unittest.TestCase):
    def test_ref_kernels(self):
        """
        Test the reference kernels against each other
        """
        random.seed(123)
        for i in range(10):
            f = Tree.generate(4)
            inp = Input.generate(f, 10, 6)
            mem = build_mem_image(f, inp)
            reference_kernel(f, inp)
            for _ in reference_kernel2(mem, {}):
                pass
            assert inp.indices == mem[mem[5] : mem[5] + len(inp.indices)]
            assert inp.values == mem[mem[6] : mem[6] + len(inp.values)]

    def test_kernel_trace(self):
        # Full-scale example for performance testing
        do_kernel_test(10, 16, 256, trace=True, prints=False)

    # Passing this test is not required for submission, see submission_tests.py for the actual correctness test
    # You can uncomment this if you think it might help you debug
    # def test_kernel_correctness(self):
    #     for batch in range(1, 3):
    #         for forest_height in range(3):
    #             do_kernel_test(
    #                 forest_height + 2, forest_height + 4, batch * 16 * VLEN * N_CORES
    #             )

    def test_kernel_cycles(self):
        # do_kernel_test(10, 16, 16, trace=True, prints=False)
        # do_kernel_test(10, 6, 8, trace=False, prints=True)
        # do_kernel_test(1, 16, 240, trace=False, prints=False)
        do_kernel_test(10, 16, 256, trace=False, prints=False)


# To run all the tests:
#    python perf_takehome.py
# To run a specific test:
#    python perf_takehome.py Tests.test_kernel_cycles
# To view a hot-reloading trace of all the instructions:  **Recommended debug loop**
# NOTE: The trace hot-reloading only works in Chrome. In the worst case if things aren't working, drag trace.json onto https://ui.perfetto.dev/
#    python perf_takehome.py Tests.test_kernel_trace
# Then run `python watch_trace.py` in another tab, it'll open a browser tab, then click "Open Perfetto"
# You can then keep that open and re-run the test to see a new trace.

# To run the proper checks to see which thresholds you pass:
#    python tests/submission_tests.py

if __name__ == "__main__":
    unittest.main()
