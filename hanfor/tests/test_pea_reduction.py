from unittest import TestCase
from req_simulator.phase_event_automaton import PhaseEventAutomaton, Phase, Transition
from collections import defaultdict
from pysmt.fnode import FNode
from pysmt.shortcuts import TRUE, And, FALSE, Or, Not, Symbol, LT, GE, LE, is_valid, Iff, is_sat, get_env

# for testing
from tests.test_req_simulator.test_counter_trace import testcases
from req_simulator.countertrace import CountertraceTransformer
from req_simulator.utils import get_countertrace_parser
from req_simulator.phase_event_automaton import build_automaton

# find SCCs - initial set of partitions
def initial_partitions(pea: PhaseEventAutomaton) -> set[frozenset[Phase]]:
    # get initial locations
    init_locs = []
    none_trans = pea.phases[None]
    for trans in none_trans:
        init_locs.append(trans.dst)

    s = []
    p = []
    c = 1
    preorders = defaultdict(int)

    return find_SCCs(pea, init_locs, s, p, c, preorders)

# Path-based strong component algorithm (https://en.wikipedia.org/wiki/Path-based_strong_component_algorithm)
def find_SCCs(pea: PhaseEventAutomaton, locs: list, s: list, p: list, c: int, preorders: defaultdict) -> set[frozenset[Phase]]:
    scc = set([])
    # 1
    v = locs.pop(0)
    preorders[v] = c
    c+=1
    # 2
    s.insert(0, v)
    p.insert(0, v)
    # 3
    for trans in pea.phases[v]:
        # 3.1
        w = trans.dst
        if preorders[w] == 0:
            locs.insert(0, w)
            scc = scc | find_SCCs(pea, locs, s, p, c, preorders)
        # 3.2
        elif w in s:
            for loc in p:
                if preorders[loc] > preorders[w]:
                    p.pop(0)
                else:
                    break
    # 4
    if v == p[0]:
        new_scc = []
        while True:
            loc = s.pop(0)
            new_scc.append(loc)
            if loc == v:
                p.pop(0)
                break
        scc.add(frozenset(new_scc))
    return scc

# refine partitions - check if all partitions are refined; send non-refined ones for refining
def get_refined_partitions(pea: PhaseEventAutomaton, parts: set[frozenset[Phase]]) -> set[frozenset[Phase]]:
    fixed_parts = set()
    broken_parts = set()
    for part in parts:
        if not is_part_refined(pea, part):
            # remove partition
            broken_parts.add(part)
            # keep fixed partitions separately
            fixed_parts = fixed_parts | refine_partition(pea, part)
    return parts.difference(broken_parts) | fixed_parts

def is_part_refined(pea: PhaseEventAutomaton, part: frozenset[Phase]) -> bool:
    if len(part) > 1:
        for i in part:
            for j in part:
                if i != j:
                    # 1
                    if i.clock_invariant != j.clock_invariant:
                        return False
                    # 2
                    transitions_i = pea.phases[i]
                    transitions_j = pea.phases[j]
                    for t_i in transitions_i:
                        for t_j in transitions_j:
                            if t_i.dst == t_j.dst and t_i.resets != t_j.resets:
                                return False
                    # 3
                    if get_formula(transitions_i) != get_formula(transitions_j):
                        return False
    return True

def get_formula(transitions: set[Transition]) -> FNode:
    # sort the transitions so the formulas match if they are the same (transition ordering added)
    return Or(*[And(transition.guard, transition.dst.state_invariant) for transition in sorted(transitions)])

# refine partition - gets an non-refined partition and refines it
def refine_partition(pea: PhaseEventAutomaton, part: frozenset[Phase]) -> set[frozenset[Phase]]:
    parts_new = []
    for loc in part:
        part_found = False
        # try to find a partition where this location can fit
        for part_new in parts_new:
            if is_part_refined(pea, frozenset(part_new + [loc])):
                part_found = True
                part_new.append(loc)
        # if no such partition exists, create a new one
        if not part_found:
            parts_new.append([loc])
    return set([frozenset(i) for i in parts_new])

# for testing
expressions, ct_str, _ = testcases['absence_between']
expressions_ = {k + '_': Symbol(v.symbol_name() + '_', v.symbol_type()) for k, v in expressions.items()}
ct = CountertraceTransformer(expressions).transform(get_countertrace_parser().parse(ct_str))
test_pea = build_automaton(ct)
init_parts = initial_partitions(test_pea)
print("\nThe initial partitions are:")
print(init_parts)
ref_parts = get_refined_partitions(pea=test_pea, parts=init_parts)
print("\nThe refined partitions are:")
print(ref_parts)

# class TestPeaReduction(TestCase):

#     # get a PEA
#     def test_pea_reduction(pea: PhaseEventAutomaton):
#         # find SCCs - initial set of partitions
#         parts = initial_partitions(pea)
#         # refine all partitions - get refined partitions
#         parts = get_refined_partitions(parts)
#         # construct pea from partitions
#         # red_pea = construct_reduced_pea(parts)
#         # check if original PEA and reduced PEA are "same"