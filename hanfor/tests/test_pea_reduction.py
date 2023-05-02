from unittest import TestCase
from req_simulator.phase_event_automaton import PhaseEventAutomaton, Phase, Transition, Sets
from collections import defaultdict
from pysmt.fnode import FNode
from pysmt.shortcuts import TRUE, And, FALSE, Or, Not, Symbol, LT, GE, LE, is_valid, Iff, is_sat, is_unsat, simplify

# for testing
from tests.test_req_simulator.test_counter_trace import testcases
from req_simulator.countertrace import CountertraceTransformer
from req_simulator.utils import get_countertrace_parser
from req_simulator.phase_event_automaton import build_automaton

# get initial locations
def get_initial_locations(pea:PhaseEventAutomaton) -> list[Phase]:
    init_locs = []
    none_trans = pea.phases[None]
    for trans in none_trans:
        init_locs.append(trans.dst)
    return init_locs

# find SCCs - initial set of partitions
def initial_partitions(pea: PhaseEventAutomaton) -> set[frozenset[Phase]]:
    s = []
    p = []
    c = 1
    preorders = defaultdict(int)

    return find_SCCs(pea, get_initial_locations(pea), s, p, c, preorders)

# Path-based strong component algorithm (https://en.wikipedia.org/wiki/Path-based_strong_component_algorithm)
def find_SCCs(pea: PhaseEventAutomaton, locs: list, s: list, p: list, c: int, preorders: defaultdict) -> set[frozenset[Phase]]:
    scc = set([])
    if len(locs) != 0:
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
                    if not check_transitions(transitions_i, transitions_j, j):
                        return False
    return True

def check_transitions(transitions_i: set[Transition], transitions_j: set[Transition], j: Phase) -> bool:
    # check weather all transitions are identical
    if len(transitions_i) != len(transitions_j):
        return False
    check_trans = set()
    for trans in transitions_i:
        check_trans.add(Transition(j, trans.dst, trans.guard, trans.resets))
    return len(transitions_j.intersection(check_trans)) != 0 and len(transitions_j.difference(check_trans)) == 0

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

def construct_reduced_pea(pea: PhaseEventAutomaton, parts: set[frozenset[Phase]]) -> PhaseEventAutomaton:
    # create empty pea
    red_pea = PhaseEventAutomaton()        

    # combine phases and add transitions - if transition already exists, dont't try to add it again
    for src_part in parts:
        src_phase = Phase(state_invariant=simplify(Or(*[loc.state_invariant for loc in src_part])),
                          clock_invariant=list(src_part)[0].clock_invariant,
                          sets=Sets(active=frozenset().union(*[loc.sets.active for loc in src_part]),
                                    gteq=frozenset().union(*[loc.sets.gteq for loc in src_part]),
                                    wait=frozenset().union(*[loc.sets.wait for loc in src_part]),
                                    less=frozenset().union(*[loc.sets.less for loc in src_part])))
        
        # initial locations
        init_locs = src_part.intersection(frozenset(get_initial_locations(pea)))
        if init_locs != frozenset():
            red_pea.add_transition(Transition(src=None,dst=src_phase, guard=Or(*[init_loc.state_invariant for init_loc in init_locs])))

        # add transitions
        loc = list(src_part)[0]
        for trans in pea.phases[loc]:
            if trans not in red_pea.phases[src_phase]:
                dst_part = get_dst_part(trans, parts)
                dst_phase = Phase(state_invariant=simplify(Or(*[loc.state_invariant for loc in dst_part])),
                                  clock_invariant=list(dst_part)[0].clock_invariant,
                                  sets=Sets(active=frozenset().union(*[loc.sets.active for loc in dst_part]),
                                            gteq=frozenset().union(*[loc.sets.gteq for loc in dst_part]),
                                            wait=frozenset().union(*[loc.sets.wait for loc in dst_part]),
                                            less=frozenset().union(*[loc.sets.less for loc in dst_part])))
                red_pea.add_transition(Transition(src=src_phase,
                                                  dst=dst_phase,
                                                  guard=simplify(And(trans.guard, trans.dst.state_invariant)),
                                                  resets=trans.resets))
    return red_pea

def get_dst_part(trans: Transition, parts: set[frozenset[Phase]]):
    for part in parts:
        for loc in part:
            if loc == trans.dst:
                return part
    return frozenset()

# for testing
class TestPEAReduction(TestCase):
    def test_pea_reduction(self):
        for testcase in testcases:
            # print(testcase)
            expressions, ct_str, _ = testcases[testcase]
            ct = CountertraceTransformer(expressions).transform(get_countertrace_parser().parse(ct_str))
            pea = build_automaton(ct)
            init_parts = initial_partitions(pea)
            # print("\nThe initial partitions are:")
            # print(init_parts)
            ref_parts = get_refined_partitions(pea=pea, parts=init_parts)
            # print("\nThe refined partitions are:")
            # print(ref_parts)
            red_pea = construct_reduced_pea(pea, ref_parts)
            
            # number of locations in reduced pea are less than or equal to the number of locations OG
            self.assertLessEqual(len(red_pea.phases.keys()), len(pea.phases.keys()))

            # has same initial locations
            self.assertTrue(And(*[loc.state_invariant.Implies(Or(*[loc_red.state_invariant for loc_red in get_initial_locations(red_pea)])) for loc in get_initial_locations(pea)]))
            
TestPEAReduction().test_pea_reduction()