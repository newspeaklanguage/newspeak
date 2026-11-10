"""Ground regressions by resolution against the ACTUAL newspeak.pl clauses.

This bounded test driver is not a general Prolog implementation or a proof of
equivalence. In particular dif/2 must be ground when reached, and unsupported
syntax fails loudly. The Lean correspondence proofs remain the proof artifact.
"""
import itertools
import re
import unittest
from dataclasses import dataclass
from pathlib import Path

import check_relational_spec as checker


@dataclass(frozen=True)
class Variable:
    identity: int


FRESH = itertools.count()
TOKEN = re.compile(r"\s*(?:('(?:[^'\\]|\\.)*')|([A-Za-z_][A-Za-z_0-9]*)|([0-9]+)|([(),\[\]|]))")


def parse(text, variables=None):
    variables = {} if variables is None else variables
    tokens = []
    cursor = 0
    while cursor < len(text.strip()):
        match = TOKEN.match(text, cursor)
        if not match:
            raise ValueError(f"unsupported test-driver syntax: {text[cursor:]}" )
        tokens.append(next(group for group in match.groups() if group is not None))
        cursor = match.end()
    index = 0

    def term():
        nonlocal index
        token = tokens[index]
        index += 1
        if token == "[":
            elements = []
            tail = ("[]", ())
            if tokens[index] != "]":
                while True:
                    elements.append(term())
                    if tokens[index] == "|":
                        index += 1
                        tail = term()
                        break
                    if tokens[index] != ",":
                        break
                    index += 1
            assert tokens[index] == "]"
            index += 1
            for element in reversed(elements):
                tail = ("cons", (element, tail))
            return tail
        if token[0].isupper() or token[0] == "_":
            if token == "_":
                return Variable(next(FRESH))
            if token not in variables:
                variables[token] = Variable(next(FRESH))
            return variables[token]
        arguments = []
        if index < len(tokens) and tokens[index] == "(":
            index += 1
            while True:
                arguments.append(term())
                if tokens[index] != ",":
                    break
                index += 1
            assert tokens[index] == ")"
            index += 1
        return (token.strip("'"), tuple(arguments))

    result = term()
    assert index == len(tokens), text
    return result


def resolve(term, substitution):
    while isinstance(term, Variable) and term in substitution:
        term = substitution[term]
    return term


def ground(term, substitution):
    term = resolve(term, substitution)
    return not isinstance(term, Variable) and all(ground(arg, substitution) for arg in term[1])


def materialize(term, substitution):
    term = resolve(term, substitution)
    if isinstance(term, Variable):
        return term
    return (term[0], tuple(materialize(arg, substitution) for arg in term[1]))


def unify(left, right, substitution):
    left, right = resolve(left, substitution), resolve(right, substitution)
    if left == right:
        return True
    if isinstance(left, Variable):
        # These fixtures are finite terms; reject a cyclic unification.
        def occurs(term):
            term = resolve(term, substitution)
            return term == left or (not isinstance(term, Variable) and any(occurs(arg) for arg in term[1]))
        if occurs(right):
            return False
        substitution[left] = right
        return True
    if isinstance(right, Variable):
        return unify(right, left, substitution)
    return left[0] == right[0] and len(left[1]) == len(right[1]) and all(
        unify(a, b, substitution) for a, b in zip(left[1], right[1]))


class GroundHornDriver:
    def __init__(self):
        self.clauses = {}
        source = Path(__file__).resolve().parents[1] / "newspeak.pl"
        for _, _, raw in checker.clauses_from(source.read_text()):
            parts = raw[:-1].split(":-", 1)
            signature = checker.term_signature(parts[0])
            self.clauses.setdefault(signature, []).append(parts)

    def solve(self, goals, substitution, depth=0):
        if depth > 200:
            raise AssertionError("test resolution depth exhausted")
        if not goals:
            yield substitution
            return
        goal, rest = resolve(goals[0], substitution), goals[1:]
        if goal[0] == "dif":
            assert all(ground(arg, substitution) for arg in goal[1]), "non-ground dif in test driver"
            if materialize(goal[1][0], substitution) != materialize(goal[1][1], substitution):
                yield from self.solve(rest, substitution, depth + 1)
            return
        for parts in self.clauses[(goal[0], len(goal[1]))]:
            variables = {}
            head = parse(parts[0].strip(), variables)
            attempt = substitution.copy()
            if unify(goal, head, attempt):
                body = [] if len(parts) == 1 else [parse(x, variables) for x in checker.split_top_level(parts[1])]
                yield from self.solve(body + rest, attempt, depth + 1)

    def results(self, query):
        variables = {}
        goals = [parse(goal, variables) for goal in checker.split_top_level(query)]
        return [materialize(variables["Result"], solution) for solution in self.solve(goals, {})]


class ApplicationStorageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.driver = GroundHornDriver()
        mixin = "mixin_def(named_class(d),store([]),[s,l],[n],i,selector(new),[],[],[])"
        cls.program = f"program(store([entry(top,t),entry(nil_object,ordinary_object(nil)),entry(mixins,store([entry(m,{mixin})])),entry(past_future_expressions,store([entry(a,self)]))]))"
        # c1 and c2 are applications of EXACTLY the same mixin m.
        classes = "store([entry(c1,class_def(m,t,nil,mc,expression(named_class(d)),none)),entry(c2,class_def(m,c1,nil,mc,expression(named_class(d)),none))])"
        activation = "activation_def(ac,initializer(i),store([]),store([]),ordinary_object(o),some(c1),none,some(a),true,store([]),store([]))"
        slots = "store([entry(slot_address(c1,s),ordinary_object(v1)),entry(slot_address(c2,s),ordinary_object(v2)),entry(slot_address(c1,l),ordinary_object(nil)),entry(slot_address(c2,l),ordinary_object(v2))])"
        cache = "store([entry(nested_cache(c1,n),k1),entry(nested_cache(c2,n),k2)])"
        obj = f"object_def(c2,{slots},{cache},none)"
        cls.heap = f"heap(store([entry(classes,{classes}),entry(objects,store([entry(o,{obj})])),entry(activations,store([entry(a,{activation})]))]))"
        cls.state = f"allocation_state({cls.heap},40,40,40,40,40)"
        cls.stack = "activation_stack_push(empty_activation_stack,activation_frame(a,empty_eval_stack))"

    def expect(self, query, expected):
        self.assertEqual(self.driver.results(query), [parse(expected)])

    def test_repeated_mixin_layout_accepted_and_disjoint(self):
        self.expect(f"instance_layout({self.program},{self.heap},c2,Result)",
                    "[slot_address(c1,s),slot_address(c1,l),slot_address(c2,s),slot_address(c2,l)]")

    def test_current_accessor_uses_selected_application(self):
        before = f"sequential_config({self.state},{self.stack},evaluate(current_read(s)))"
        after = f"sequential_config({self.state},{self.stack},evaluate(read_slot(o,slot_address(c1,s))))"
        self.expect(f"object_slot_step({self.program},{before},Result)", after)

    def test_reads_same_declaration_are_independent(self):
        for application, value in (("c1", "v1"), ("c2", "v2")):
            self.expect(f"read_object_slot_value({self.heap},o,slot_address({application},s),Result)", f"ordinary_object({value})")

    def test_write_does_not_change_other_application(self):
        self.expect(f"write_object_slot_heap({self.heap},o,slot_address(c1,s),ordinary_object(new),Updated),read_object_slot_value(Updated,o,slot_address(c2,s),Result)", "ordinary_object(v2)")

    def test_lazy_miss_uses_own_nil_cell_not_other_cached_value(self):
        before = f"sequential_config({self.state},{self.stack},evaluate(lazy_read(l,self)))"
        frames = "eval_stack_push(empty_eval_stack,lazy_slot_store(o,slot_address(c1,l)))"
        after = f"sequential_config({self.state},activation_stack_push(empty_activation_stack,activation_frame(a,{frames})),evaluate(self))"
        self.expect(f"object_slot_step({self.program},{before},Result)", after)

    def test_simultaneous_expansion_qualifies_both_phases(self):
        self.expect(f"slot_sim_code({self.program},a,o,c1,[immutable_slot(s,self,q)],Result)",
                    "[write_slot(o,slot_address(c1,s),ordinary_send(self,selector('computing:'),[closure_literal(q)])),ordinary_send(read_slot(o,slot_address(c1,s)),selector(resolve),[])]")

    def test_sequential_initializer_captures_selected_application(self):
        before = f"sequential_config({self.state},{self.stack},initialize_sequential_slots(o,[immutable_slot(s,self,q)],[],[]))"
        frames = "eval_stack_push(empty_eval_stack,store_initialized_slot(o,slot_address(c1,s),[],[],[]))"
        after = f"sequential_config({self.state},activation_stack_push(empty_activation_stack,activation_frame(a,{frames})),evaluate(self))"
        self.expect(f"slot_initialization_step({self.program},{before},Result)", after)

    def test_nested_cache_uses_selected_application(self):
        before = f"sequential_config({self.state},{self.stack},evaluate(nested_class(n,self)))"
        after = f"sequential_config({self.state},{self.stack},object(class_object(k1)))"
        self.expect(f"nested_class_step({self.program},{before},Result)", after)

    def test_nested_cache_write_does_not_change_other_application(self):
        self.expect(f"write_nested_class_heap({self.heap},o,nested_cache(c1,n),new,Updated),read_nested_class(Updated,o,nested_cache(c2,n),Result)", "some(k2)")


if __name__ == "__main__":
    unittest.main()
