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

    def build_vhash(self, val_hash_addr_v, vtmp1, vtmp2, round, i):
        slots = []
        for hi, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            # slots.append(("valu", MultiSlot(slots=((op1, vtmp1, val_hash_addr_v, self.scratch_const(val1)),(op3, vtmp2, val_hash_addr_v, self.scratch_const(val3))))))
            slots.append(("valu", ("vbroadcast", vtmp1, self.scratch_const(val1))))
            slots.append(("valu", (op1, vtmp1, val_hash_addr_v, vtmp1)))
            
            slots.append(("valu", ("vbroadcast", vtmp2, self.scratch_const(val3))))
            slots.append(("valu", (op3, vtmp2, val_hash_addr_v,vtmp2)))

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
        tmp2 = self.alloc_scratch("tmp2")
        tmp3 = self.alloc_scratch("tmp3")
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
        
        body = []  # array of slots

        vsize = 8

        # Scalar scratch registers
        # tmp_idx = self.alloc_scratch("tmp_idx")
        # tmp_val = self.alloc_scratch("tmp_val")
        # tmp_node_val = self.alloc_scratch("tmp_node_val")
        tmp_addr = self.alloc_scratch("tmp_addr")

        # Vector scratch registers
        vtmp1 = self.alloc_scratch("vtmp1", vsize)
        vtmp2 = self.alloc_scratch("vtmp2", vsize)
        vtmp3 = self.alloc_scratch("vtmp3", vsize)

        tmp_idx_v = self.alloc_scratch('tmp_idx_v', vsize)
        vtmp_idx        = [tmp_idx_v+x for x in range(vsize)]

        tmp_val_v = self.alloc_scratch('tmp_val_v', vsize)
        vtmp_val        = [tmp_val_v+x for x in range(vsize)]

        tmp_node_val_v = self.alloc_scratch('tmp_node_val_v', vsize)
        vtmp_node_val   = [tmp_node_val_v+x for x in range(vsize)]

        tmp_addr_v = self.alloc_scratch('tmp_addr_v', vsize)
        vtmp_addr       = [tmp_addr_v+x for x in range(vsize)]

        for round in range(rounds):
            assert batch_size % vsize == 0
            for i in range(0, batch_size, vsize):
                # print(f'round {i}')
                i_const = self.scratch_const(i)
                # idx = mem[inp_indices_p + i]
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_indices_p"], i_const)))
                body.append(("load", ("vload", tmp_idx_v, tmp_addr)))

                # val = mem[inp_values_p + i]
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_values_p"], i_const)))
                body.append(("load", ("vload", tmp_val_v, tmp_addr)))


                for j in range(vsize):
                    i_j_const = self.scratch_const(i+j)
                    # body.append(("debug", ("compare", vtmp_val[j], (round, i, "val"))))
                    # node_val = mem[forest_values_p + idx]
                    body.append(("alu", ("+", vtmp_addr[j], self.scratch["forest_values_p"], vtmp_idx[j])))
                    body.append(("load", ("load", vtmp_node_val[j], vtmp_addr[j])))

                    # body.append(("debug", ("compare", vtmp_node_val[j], (round, i, "node_val"))))
                    # val = myhash(val ^ node_val)
                    # body.append(("alu", ("^", vtmp_val[j], vtmp_val[j], vtmp_node_val[j])))
                    # body.extend(self.build_hash(vtmp_val[j], tmp1, tmp2, round, i))

                # val = myhash(val ^ node_val)
                body.append(("valu", ("^", tmp_val_v, tmp_val_v, tmp_node_val_v)))
                body.extend(self.build_vhash(tmp_val_v, vtmp1, vtmp2, round, i))
                self.add("debug", ("comment", "Vhash finished"))
                    # body.append(("debug", ("compare", vtmp_val[j], (round, i, "hashed_val"))))
                
                # idx = 2*idx + (1 if val % 2 == 0 else 2)
                body.append(("valu", ("vbroadcast", vtmp1, two_const)))
                body.append(("valu", ("%", vtmp1, tmp_val_v, vtmp1)))

                body.append(("valu", ("vbroadcast", vtmp2, zero_const)))
                body.append(("valu", ("==", vtmp1, vtmp1, vtmp2)))

                body.append(("valu", ("vbroadcast", vtmp2, one_const)))
                body.append(("valu", ("vbroadcast", vtmp3, two_const)))
                body.append(("flow", ("vselect", vtmp1, vtmp1, vtmp2, vtmp3)))

                body.append(("valu", ("multiply_add", tmp_idx_v, tmp_idx_v, vtmp3, vtmp1)))

                # TODO - this can be mitigated
                body.append(("valu", ("vbroadcast", vtmp2, zero_const)))
                body.append(("valu", ("vbroadcast", vtmp3, self.scratch["n_nodes"])))
                body.append(("valu", ("<", vtmp1, tmp_idx_v, vtmp3)))
                body.append(("flow", ("vselect", tmp_idx_v, vtmp1, tmp_idx_v, vtmp2)))

                for j in range(vsize):
                    i_j_const = self.scratch_const(i+j)
                    # body.append(("alu", ("%", tmp1, vtmp_val[j], two_const)))
                    # body.append(("alu", ("==", tmp1, tmp1, zero_const)))
                    # body.append(("flow", ("select", tmp3, vtmp1+j, one_const, two_const)))
                    # body.append(("alu", ("*", vtmp_idx[j], vtmp_idx[j], two_const)))
                    # body.append(("alu", ("+", vtmp_idx[j], vtmp_idx[j], vtmp1+j)))
                    # body.append(("debug", ("compare", vtmp_idx[j], (round, i, "next_idx"))))

                    # idx = 0 if idx >= n_nodes else idx
                    # body.append(("alu", ("<", tmp1, vtmp_idx[j], self.scratch["n_nodes"])))
                    # body.append(("flow", ("select", vtmp_idx[j], tmp1, vtmp_idx[j], zero_const)))
                    # body.append(("debug", ("compare", vtmp_idx[j], (round, i, "wrapped_idx"))))
                # # mem[inp_indices_p + i] = idx
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_indices_p"], i_const)))
                body.append(("store", ("vstore", tmp_addr, tmp_idx_v)))
                # # mem[inp_values_p + i] = val
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_values_p"], i_const)))
                body.append(("store", ("vstore", tmp_addr, tmp_val_v)))

        body_instrs = self.build_multi(body)
        self.instrs.extend(body_instrs)
        # Required to match with the yield in reference_kernel2
        self.instrs.append({"flow": [("pause",)]})

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
        # do_kernel_test(1, 1, 8, trace=True, prints=True)
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
