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
    # def __iter__(self):
    #     return iter(self.slots)
    # def __getitem__(self, key) -> tuple:
    #     return self.slots[key]


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
        print(f'{len(body)=} {round_length=} {batches=}')

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


    def add(self, engine, slot):
        self.instrs.append({engine: [slot]})

    def alloc_scratch(self, name=None, length=1):
        addr = self.scratch_ptr
        assert name not in self.scratch
        if name is not None:
            self.scratch[name] = addr
            # print(f'adding {name=} to the debug scratchmap')
            self.scratch_debug[addr] = (name, length)
        self.scratch_ptr += length
        assert self.scratch_ptr <= SCRATCH_SIZE, "Out of scratch space"
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


        self.mb_size = 6

        # Scalar scratch registers
        # tmp_idx = self.alloc_scratch("tmp_idx")
        # tmp_val = self.alloc_scratch("tmp_val")
        # tmp_node_val = self.alloc_scratch("tmp_node_val")
        arr_tmp_addr_idx = [self.alloc_scratch(f'tmp_addr_idx_{i}') for i in range(self.mb_size)]
        arr_tmp_addr_val = [self.alloc_scratch(f'tmp_addr_val_{i}') for i in range(self.mb_size)]

        # Vector scratch registers
        arr_vtmp1 = [self.alloc_scratch(f'vtmp1_{i}', VLEN) for i in range(self.mb_size)]
        arr_vtmp2 = [self.alloc_scratch(f'vtmp2_{i}', VLEN) for i in range(self.mb_size)]

        arr_tmp_idx_v       = [self.alloc_scratch(f'tmp_idx_v_{i}', VLEN) for i in range(self.mb_size)]
        arr_tmp_val_v       = [self.alloc_scratch(f'tmp_val_v_{i}', VLEN) for i in range(self.mb_size)]
        arr_tmp_node_val_v  = [self.alloc_scratch(f'tmp_node_val_v_{i}', VLEN) for i in range(self.mb_size)]
        arr_tmp_addr_v      = [self.alloc_scratch(f'tmp_addr_v_{i}', VLEN) for i in range(self.mb_size)]

        vbatch_size = int(batch_size/VLEN)
        mega_idx_v = [self.alloc_scratch(f'mega_idx_v_{i}', VLEN) for i in range(vbatch_size)]
        mega_val_v = [self.alloc_scratch(f'mega_val_v_{i}', VLEN) for i in range(vbatch_size)]

        vzero = self.alloc_scratch('vzero', VLEN)
        vone = self.alloc_scratch('vone', VLEN)
        vtwo = self.alloc_scratch('vtwo', VLEN)
        vn_nodes = self.alloc_scratch('vn_nodes', VLEN)
        vforest_values_p = self.alloc_scratch('vforest_values_p', VLEN)

        self.add("valu", ("vbroadcast", vzero, zero_const))
        self.add("valu", ("vbroadcast", vone, one_const))
        self.add("valu", ("vbroadcast", vtwo, two_const))
        self.add("valu", ("vbroadcast", vn_nodes, self.scratch['n_nodes']))
        self.add("valu", ("vbroadcast", vforest_values_p, self.scratch['forest_values_p']))

        for i in self.init_hash():
            self.add(*i)

        assert batch_size % VLEN == 0

        body = []
        for i in range(0, batch_size, VLEN):
            vbatch = int(i/VLEN)
            mb_num = vbatch % self.mb_size

            tmp_addr_idx = arr_tmp_addr_idx[mb_num]
            tmp_addr_val = arr_tmp_addr_val[mb_num]

            tmp_idx_v = mega_idx_v[vbatch]
            tmp_val_v = mega_val_v[vbatch]

            i_const = self.scratch_const(i)
            # idx = mem[inp_indices_p + i]
            # val = mem[inp_values_p + i]
            body.append(("alu", MultiSlot(slots=(("+", tmp_addr_idx, self.scratch["inp_indices_p"], i_const),
                ("+", tmp_addr_val, self.scratch["inp_values_p"], i_const)))))
            body.append(("load",MultiSlot(slots= (("vload", tmp_idx_v, tmp_addr_idx),("vload", tmp_val_v, tmp_addr_val)))))
        
        body_instrs = self.build_compress(body, batch_size, 1)
        self.instrs.extend(body_instrs)


        body = []  # array of slots
        round_num = -1
        for round in range(rounds):
            for i in range(0, batch_size, VLEN):
                vbatch = int(i/VLEN)
                round_num += 1
                # mb_num = vbatch % self.mb_size
                mb_num = round_num % self.mb_size

                vtmp1 = arr_vtmp1[mb_num]
                vtmp2 = arr_vtmp2[mb_num]

                tmp_idx_v = mega_idx_v[vbatch]
                tmp_val_v = mega_val_v[vbatch]

                tmp_node_val_v = arr_tmp_node_val_v[mb_num]
                tmp_addr_v = arr_tmp_addr_v[mb_num]

                body.append(("valu", ("+", tmp_addr_v, tmp_idx_v, vforest_values_p)))
                for j in range(VLEN):
                    # node_val = mem[forest_values_p + idx]
                    body.append(("load", ("load_offset", tmp_node_val_v, tmp_addr_v, j)))

                # val = myhash(val ^ node_val)
                body.append(("valu", ("^", tmp_val_v, tmp_val_v, tmp_node_val_v)))
                body.extend(self.build_vhash(tmp_val_v, vtmp1, vtmp2, round, i))
                self.add("debug", ("comment", "Vhash finished"))
                

                # idx = 2*idx + (1 if val % 2 == 0 else 2)
                body.append(("valu", ("%", vtmp1, tmp_val_v, vtwo)))
                body.append(("valu", ("+", vtmp1, vtmp1, vone)))
                body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtwo, vtmp1)))

                # idx = 0 if idx >= n_nodes else idx
                body.append(("valu", ("<", vtmp1, tmp_idx_v, vn_nodes)))
                body.append(("flow", ("vselect", tmp_idx_v, vtmp1, tmp_idx_v, vzero)))
                
        # now combine everything
        # body_instrs = self.build_multi(body)
        body_instrs = self.build_compress(body, batch_size, rounds)
        self.instrs.extend(body_instrs)


        body = []
        for i in range(0, batch_size, VLEN):
            vbatch = int(i/VLEN)
            mb_num = vbatch % self.mb_size

            tmp_addr_idx = arr_tmp_addr_idx[mb_num]
            tmp_addr_val = arr_tmp_addr_val[mb_num]

            tmp_idx_v = mega_idx_v[vbatch]
            tmp_val_v = mega_val_v[vbatch]

            i_const = self.scratch_const(i)
            # mem[inp_indices_p + i] = idx
            # mem[inp_values_p + i] = val
            body.append(("alu", MultiSlot(slots=(("+", tmp_addr_idx, self.scratch["inp_indices_p"], i_const),
                                            ("+", tmp_addr_val, self.scratch["inp_values_p"], i_const)))))
            body.append(("store", MultiSlot(slots=(("vstore", tmp_addr_idx, tmp_idx_v), 
                                            ("vstore", tmp_addr_val, tmp_val_v)))))

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

        print(f'scratch used: {self.scratch_ptr=}')

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
        # do_kernel_test(1, 2, 64, trace=True, prints=True)
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
