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

def addresses(slot):
    return slot[1:] if slot[0] != 'load_offset' else slot[1:-1]

class OptimizedInstruction():
    e: str
    slots: tuple
    written_scratch: List[tuple]

    def __init__(self, e):
        self.e = e
        self.slots = []
        self.written_scratch = [(0,0)]

    def inst_length(self, e):
        lengths = {
            'alu' : 1,
            'valu' : 8,
            'load' : 1,
            'vload' : 8
            }
        return lengths[e]

    def slot_overlaps(self, e, slot):
        offset = 0 if slot[0] != 'load_offset' else slot[3]
        length = self.inst_length(e)
        taddr = slot[1] + offset

        overlap = False
        # assert len(self.written_scratch) < 20, f'written_scratch is large'
        for a, l in self.written_scratch:
            o, _ = areas_overlap(a, l, taddr, length)
            if o:
                overlap = True
        saddrs = slot[2:] if slot[0] != 'load_offset' else slot[2:-1]
        for saddr in saddrs:
            saddr += offset
            for a,l in self.written_scratch:
                o, _ =  areas_overlap(a, l, saddr, length)
                if o:
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

    def insert_area(self, slot):
        offset = 0 if slot[0] != 'load_offset' else slot[3]
        length = self.inst_length(self.e)
        taddr = slot[1] + offset
        found = False
        for saddr, slength in self.written_scratch:
            if areas_adjacent(taddr, length, saddr, slength):
                found = True
                self.written_scratch.remove((saddr, slength))
                self.written_scratch.append((min(saddr, taddr),max(taddr+length,saddr+slength)-min(saddr, taddr)))
                break
        if not found:
            self.written_scratch.append((taddr, length))

    def add_and_register(self, e, slot) -> bool:
        assert self.permitted(e, slot), f'Trying to add an unpermitted instruction'
        self.slots.append(slot)
        self.register(slot)

     

    def register(self, slot):
        if len(self.slots) < SLOT_LIMITS[self.e]:
            self.insert_area(slot)

    def full(self) -> bool:
        return len(self.slots) == SLOT_LIMITS[self.e]

    def build(self):
        return {self.e: self.slots}

    


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

    

    def compile(self):
        stock = [self.decompose(i) for i in self.input]
        buffer = []
        if self.debug:
            print('\n'.join([f'{i}' for i in stock]))
        # stock.reverse()

        optimized = []
        last_seen = {}
        for s in stock:
            if self.debug:
                print(f'optimizing {s}')
            e = s[0]
            for slot in s[1]:
                found = False
                # iterate optimized, and find a non-coliding spot
                seen = [0]
                for a in addresses(slot):
                    if a in last_seen:
                        seen.append(last_seen[a])
                i = max(seen)
                while i < len(optimized) and not found:
                    opz = optimized[i]
                    if opz.permitted(e, slot):
                        opz.add_and_register(e, slot)
                        found = True
                        break
                    # if e == 'load' and opz.e in ['valu', 'alu']:
                    #     if not opz.slot_overlaps(e, slot):
                    #         nopz = OptimizedInstruction(e)
                    #         nopz.add_and_register(e, slot)
                    #         optimized = optimized[:i] + [nopz] + optimized[i:]
                    #         found = True
                    #         for addr in last_seen:
                    #             if last_seen[addr] > i:
                    #                 last_seen[addr] = last_seen[addr]+1
                    #         break

                    opz.register(slot)
                    
                    i += 1
                if not found:
                    opz = OptimizedInstruction(e)
                    opz.add_and_register(e, slot)
                    optimized.append(opz)
                # update last_seen
                for addr in addresses(slot):
                    last_seen[addr] = i

            # if optimized[0].full():
            #     self.output.append(optimized[0].build())
            #     optimized = optimized[0:]   

        self.output.extend([opz.build() for opz in optimized])

        if self.debug:
            print('done compiling')
            print('\n'.join([f'{i}' for i in self.output]))


                
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
            # slots.append(("alu", (op1, tmp1, val_hash_addr, self.scratch_const(val1))))
            # slots.append(("alu", (op3, tmp2, val_hash_addr, self.scratch_const(val3))))

            slots.append(("alu", MultiSlot(slots=((op1, tmp1, val_hash_addr, self.scratch_const(val1)),(op3, tmp2, val_hash_addr, self.scratch_const(val3))))))
            slots.append(("alu", (op2, val_hash_addr, tmp1, tmp2)))
            # slots.append(("debug", ("compare", val_hash_addr, (round, i, "hash_stage", hi))))

        return slots

    def init_hash(self):
        self.hash_consts = {}
        slots = []
        for hi, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            const1 = self.alloc_scratch(f'hash_val1_{hi}', VLEN)
            slots.append(("valu", ("vbroadcast", const1, self.scratch_const(val1))))

            const3 = self.alloc_scratch(f'hash_val3_{hi}', VLEN)
            slots.append(("valu", ("vbroadcast", const3, self.scratch_const(val3))))

            self.hash_consts[hi] = (const1, const3)
        return slots

    def build_vhash(self, val_hash_addr_v, vtmp1, vtmp2, round, i):
        slots = []
        for hi, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            const1, const3 = self.hash_consts[hi]
            slots.append(("valu", MultiSlot(slots=((op1, vtmp1, val_hash_addr_v, const1),(op3, vtmp2, val_hash_addr_v,const3)))))
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

        # extra_room_p = self.alloc_scratch("extra_room_p")
        # self.add("load", ("const", extra_room_p, 7))
        # self.add("alu", ("+", extra_room_p, extra_room_p, self.scratch['n_nodes']))
        # self.add("alu", ("+", extra_room_p, extra_room_p, self.scratch['batch_size']))
        # self.add("alu", ("+", extra_room_p, extra_room_p, self.scratch['batch_size']))


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

        CONSTS = 9
        const_int = [zero_const, one_const, two_const] + [self.scratch_const(i) for i in range(3,CONSTS)]
        vconst = [self.alloc_scratch(f'vconst{i}', VLEN) for i in range(CONSTS)]
        for i in range(CONSTS):
            self.add("valu", ("vbroadcast", vconst[i], const_int[i]))

        vone = vconst[1]
        vtwo = vconst[2]

        self.mb_size = 6
        vbatch_size = int(batch_size/VLEN)

        # Scalar scratch registers
        # tmp_idx = self.alloc_scratch("tmp_idx")
        # tmp_val = self.alloc_scratch("tmp_val")
        # tmp_node_val = self.alloc_scratch("tmp_node_val")
        # arr_tmp_addr_idx = [self.alloc_scratch(f'tmp_addr_idx_{i}') for i in range(self.mb_size)]
        # arr_tmp_addr_val = [self.alloc_scratch(f'tmp_addr_val_{i}') for i in range(self.mb_size)]

        # Vector scratch registers
        arr_vtmp1 = [self.alloc_scratch(f'vtmp1_{i}', VLEN) for i in range(vbatch_size)]
        arr_vtmp2 = [self.alloc_scratch(f'vtmp2_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp3 = [self.alloc_scratch(f'vtmp3_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp4 = [self.alloc_scratch(f'vtmp4_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp5 = [self.alloc_scratch(f'vtmp5_{i}', VLEN) for i in range(self.mb_size)]

        # arr_tmp_idx_v       = [self.alloc_scratch(f'tmp_idx_v_{i}', VLEN) for i in range(self.mb_size)]
        # arr_tmp_val_v       = [self.alloc_scratch(f'tmp_val_v_{i}', VLEN) for i in range(self.mb_size)]
        arr_tmp_node_val_v  = [self.alloc_scratch(f'tmp_node_val_v_{i}', VLEN) for i in range(self.mb_size)]
        # arr_tmp_addr_v      = [self.alloc_scratch(f'tmp_addr_v_{i}', VLEN) for i in range(self.mb_size)]

        
        mega_idx_v = [self.alloc_scratch(f'mega_idx_v_{i}', VLEN) for i in range(vbatch_size)]
        mega_val_v = [self.alloc_scratch(f'mega_val_v_{i}', VLEN) for i in range(vbatch_size)]


        # vn_nodes = self.alloc_scratch('vn_nodes', VLEN)
        vforest_values_p = self.alloc_scratch('vforest_values_p', VLEN)


        # self.add("valu", ("vbroadcast", vn_nodes, self.scratch['n_nodes']))
        self.add("valu", ("vbroadcast", vforest_values_p, self.scratch['forest_values_p']))
        # The need to decrease here is because we are managing tmp_idx_v as 1-base instead of 0-base
        self.add("valu", ("-", vforest_values_p, vforest_values_p, vone))

        vtree = self.alloc_scratch('vtree', VLEN*4)
        ptr = arr_vtmp1[0]
        self.add("alu", ("+", ptr, self.scratch['forest_values_p'], const_int[0]))
        for i in range(4):
            self.add("load", ("vload", vtree+i*VLEN, ptr))
            if i != 3:
                self.add("alu", ("+", ptr, ptr, const_int[8]))

        # self.add("load", ("vload", vtree, self.scratch['forest_values_p']))
        # self.add("alu", ("+", arr_vtmp1[0], self.scratch['forest_values_p'], const_int[8]))
        # self.add("load", ("vload", vtree+8, arr_vtmp1[0]))


        NUM_STORED_VF = 2**5-1

        vforest_values = [self.alloc_scratch(f'vf{i}', VLEN) for i in range(NUM_STORED_VF)]
        for i in range(NUM_STORED_VF):
            self.add("valu", ("vbroadcast", vforest_values[i], vtree+i))

        vf = vforest_values


        for i in range(2, NUM_STORED_VF, 2):
            self.add("valu", ("-", vforest_values[i], vforest_values[i], vforest_values[i-1]))

        for i in self.init_hash():
            self.add(*i)

        assert batch_size % VLEN == 0

        body = []
        for i in range(0, batch_size, VLEN):
            vbatch = int(i/VLEN)
            mb_num = vbatch % self.mb_size

            vtmp2 = arr_vtmp2[mb_num]

            tmp_idx_v = mega_idx_v[vbatch]
            tmp_val_v = mega_val_v[vbatch]

            i_const = self.scratch_const(i)
            # idx = mem[inp_indices_p + i]
            # val = mem[inp_values_p + i]
            # No need to initialize tmp_idx_v because it is zeros in the first place
            body.append(("alu", ("+", vtmp2, self.scratch["inp_values_p"], i_const)))
            body.append(("load",("vload", tmp_val_v, vtmp2)))
            # Initializing to one for easier usage
            body.append(("valu", ("+", tmp_idx_v, tmp_idx_v, vone)))
        
        body_instrs = self.build_compress(body, batch_size, 1)
        # body_instrs = self.compile(body)
        self.instrs.extend(body_instrs)

        # tmp_node_val_v initiation method
        BROADCAST_ZERO = 0
        LOAD_ONE = 1
        LOAD_TWO = 2
        LOAD_THREE = 3
        LOAD_FOUR = 4
        AFTER_WRAPAROUND = 777
        NORMAL_LOAD = 999

        # idx iteration method
        WRAPAROUND = "wraparound"
        NORMAL_ITERATE = "normal_iterate"

        # rounds, tmp_node_val-method, iter-method
        COMPUTE_STAGES = [
            # First round, load tmp_node_val_v using broadcast
            [1,                          BROADCAST_ZERO,          NORMAL_ITERATE],    # BROADCAST_ZERO
            [1,                          LOAD_ONE,          NORMAL_ITERATE], # LOAD_ONE
            [1,                          LOAD_TWO,          NORMAL_ITERATE], # LOAD_TWO
            [1,                          LOAD_THREE,          NORMAL_ITERATE], 
            [1,                          LOAD_FOUR,          NORMAL_ITERATE], 
            # Run until wrap-around
            [forest_height - 5,          NORMAL_LOAD,          NORMAL_ITERATE],
            # Wrap around
            [1,                          NORMAL_LOAD,          WRAPAROUND],
            # First round after wraparound
            [1,                          BROADCAST_ZERO,          NORMAL_ITERATE],    # BROADCAST_ZERO
            [1,                          LOAD_ONE,          NORMAL_ITERATE], # LOAD_ONE
            [1,                          LOAD_TWO,          NORMAL_ITERATE], # LOAD_TWO
            [1,                          LOAD_THREE,          NORMAL_ITERATE],
            [1,                          LOAD_FOUR,          NORMAL_ITERATE], 
            # Last set of rounds
            # [rounds - forest_height - 5, NORMAL_LOAD,       NORMAL_ITERATE],
        ]

        # for a,l in self.scratch_debug.values():
        #     print(f'name={a} length={l}')
        stage = 0
        for rounds_here, load_method, iterate_method in COMPUTE_STAGES:
            body = []  # array of slots
            round_num = -1
            stage += 1
            for round in range(rounds_here):
                for i in range(0, batch_size, VLEN):
                    vbatch = int(i/VLEN)
                    round_num += 1
                    # mb_num = vbatch % self.mb_size
                    mb_num = round_num % self.mb_size

                    vtmp1 = arr_vtmp1[vbatch]
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
                            # vtmp1 has the value we need from the previous iteration
                            body.append(("valu", ("multiply_add", tmp_node_val_v, vtmp1, vf[2], vf[1])))
                        case x if x == LOAD_TWO:

                            # vtmp1 has the value we need from the previous iteration
                            body.append(("valu", MultiSlot(slots=(
                                    ("multiply_add", tmp_node_val_v, vtmp1, vf[4], vf[3]),
                                    ("multiply_add", vtmp2,          vtmp1, vf[6], vf[5]),
                                    ("&", vtmp1, tmp_idx_v, vconst[2])
                                ))))

                            body.append(("valu", MultiSlot(slots=(
                                   ("-", vtmp2, vtmp2, tmp_node_val_v),
                                   (">>",vtmp1, vtmp1, vconst[1])
                                   
                                ))))

                            body.append(("valu", ("multiply_add", tmp_node_val_v, vtmp1, vtmp2, tmp_node_val_v)))

                        case x if x == LOAD_THREE:

                            tvector = [vtmp5, vtmp2, vtmp3, vtmp4]
                            base = 7
                            slots = []
                            for i in range(4):
                                slots.append(("multiply_add", tvector[i], vtmp1, vf[base+i*2+1], vf[base+i*2]))
                            body.append(("valu", MultiSlot(slots=slots)))
  
                            slots = []
                            for i in range(2):
                                slots.append(("-", tvector[i*2+1], tvector[i*2+1], tvector[i*2]))
                            body.append(("valu", MultiSlot(slots=slots)))

                            body.append(("valu", ("&", vtmp1, tmp_idx_v, vconst[2])))
                            body.append(("valu", (">>",vtmp1, vtmp1,     vconst[1])))

                            slots = []
                            for i in range(2):
                                slots.append(("multiply_add", tvector[i*2+1], vtmp1, tvector[i*2+1], tvector[i*2]))
                            body.append(("valu", MultiSlot(slots=slots)))

                            tvector = [vtmp2, vtmp4]

                            body.append(("valu", ("-", tvector[1], tvector[1], tvector[0])))
                            body.append(("valu", ("&", vtmp1, tmp_idx_v, vconst[4])))
                            body.append(("valu", (">>",vtmp1, vtmp1, vconst[2])))


                            body.append(("valu", ("multiply_add",tmp_node_val_v, vtmp1, tvector[1], tvector[0])))

                        case x if x == LOAD_FOUR:
                            
                            # body.append(("valu", ("+", tmp_node_val_v, vconst[0], vconst[0])))

                            outputs = [tmp_node_val_v, vtmp2]
                            for offset in range(2):
                                if offset > 0:
                                    body.append(("valu", ("&", vtmp1, tmp_idx_v, vconst[1])))

                                base = 15+offset*8
                                tvector = [vtmp2, vtmp3, vtmp4, vtmp5]
                                slots = []
                                if offset == 0:
                                    slots.append(("+", tmp_node_val_v, vconst[0], vconst[0]))
                                # if offset > 0:
                                #     slots.append(("&", vtmp1, tmp_idx_v, vconst[1]))
                                for i in range(4):
                                    slots.append(("multiply_add", tvector[i], vtmp1, vf[base+i*2+1], vf[base+i*2]))
                                body.append(("valu", MultiSlot(slots=slots)))

                                slots = []
                                for i in range(2):
                                    slots.append(("-", tvector[i*2+1], tvector[i*2+1], tvector[i*2]))
                                body.append(("valu", MultiSlot(slots=slots)))

                                body.append(("valu", ("&", vtmp1, tmp_idx_v, vconst[2])))
                                body.append(("valu", (">>",vtmp1, vtmp1,     vconst[1])))

                                slots = []
                                for i in range(2):
                                    slots.append(("multiply_add", tvector[i*2+1], vtmp1, tvector[i*2+1], tvector[i*2]))
                                body.append(("valu", MultiSlot(slots=slots)))

                                tvector = [vtmp3, vtmp5]

                                body.append(("valu", ("-", tvector[1], tvector[1], tvector[0])))
                                body.append(("valu", ("&", vtmp1, tmp_idx_v, vconst[4])))
                                body.append(("valu", (">>",vtmp1, vtmp1,     vconst[2])))

                                body.append(("valu", ("multiply_add",outputs[offset], vtmp1, tvector[1], tvector[0])))
                                
                            tvector = [outputs[0], outputs[1]]
                            body.append(("valu", ("-", tvector[1], tvector[1], tvector[0])))
                            body.append(("valu", ("&", vtmp1, tmp_idx_v, vconst[8])))
                            body.append(("valu", (">>",vtmp1, vtmp1,     vconst[3])))
                            body.append(("valu", ("multiply_add",tmp_node_val_v, vtmp1, tvector[1], tvector[0])))

                            
                            
                            # load 4 vectors of tree
                            # for each item - check against idx value, and add
                        case x if x == NORMAL_LOAD:
                            body.append(("valu", ("+", vtmp2, tmp_idx_v, vforest_values_p)))
                            for j in range(VLEN):
                                # node_val = mem[forest_values_p + idx]
                                body.append(("load", ("load_offset", tmp_node_val_v, vtmp2, j)))


                    # val = myhash(val ^ node_val)
                    if load_method == BROADCAST_ZERO:
                        body.append(("valu", ("^", tmp_val_v, tmp_val_v, vf[0])))
                    else:
                        body.append(("valu", ("^", tmp_val_v, tmp_val_v, tmp_node_val_v)))
                    body.extend(self.build_vhash(tmp_val_v, vtmp1, vtmp2, round, i))
                    self.add("debug", ("comment", "Vhash finished"))

                    match iterate_method:
                        case x if x == NORMAL_ITERATE:
                            # idx = 2*idx + (1 if val % 2 == 0 else 2)
                            # Not needed for wrap-around because it always happens in the middle iteration
                            body.append(("valu", ("%", vtmp1, tmp_val_v, vtwo)))
                            body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vtmp1)))
                        case x if x == WRAPAROUND:
                            # all goes to one               
                            # body.append(("valu", ("vbroadcast", tmp_idx_v, zero_const)))
                            body.append(("valu", ("*", tmp_idx_v, vone, vone)))

            # now combine everything
            # body_instrs = self.build_multi(body)
            if stage == 6 or True:
                body_instrs = self.compile(body, True)
                print(f'before: {len(body)}')
                print(f'after:  {len(body_instrs)}')
            else:
                body_instrs = self.build_compress(body, batch_size, rounds_here)
            self.instrs.extend(body_instrs)  

        body = []
        for i in range(0, batch_size, VLEN):
            vbatch = int(i/VLEN)
            mb_num = vbatch % self.mb_size

            vtmp1 = arr_vtmp1[mb_num]
            vtmp2 = arr_vtmp2[mb_num]

            tmp_idx_v = mega_idx_v[vbatch]
            tmp_val_v = mega_val_v[vbatch]

            # one last +1
            body.append(("valu", ("-", tmp_idx_v, tmp_idx_v, vone)))

            i_const = self.scratch_const(i)
            # mem[inp_indices_p + i] = idx
            # mem[inp_values_p + i] = val

            body.append(("alu", MultiSlot(slots=(("+", vtmp1, self.scratch["inp_indices_p"], i_const),
                                            ("+", vtmp2, self.scratch["inp_values_p"], i_const)))))
            body.append(("store", MultiSlot(slots=(("vstore", vtmp1, tmp_idx_v), 
                                            ("vstore", vtmp2, tmp_val_v)))))

        body_instrs = self.build_compress(body, batch_size, 1)
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
        assert (
            machine.mem[inp_values_p : inp_values_p + len(inp.values)]
            == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
        ), f"Incorrect result on round {i}"
        inp_indices_p = ref_mem[5]
        if prints:
            print(machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)])
            print(ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)])
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
