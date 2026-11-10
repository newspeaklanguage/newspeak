import unittest

from class_init_model import Mixin, PullFuture, Runtime


class ClassInitializationTests(unittest.TestCase):
    def test_class_evaluation_is_fresh_but_reuses_static_mixin(self):
        runtime = Runtime()
        mixin = Mixin("M")
        c1 = runtime.new_class(mixin, None, "eo")
        c2 = runtime.new_class(mixin, None, "eo")
        self.assertIs(c1.mixin, c2.mixin)
        self.assertNotEqual(c1.identity, c2.identity)
        self.assertNotEqual(c1.metaclass, c2.metaclass)

    def test_mixin_application_copies_source_enclosing_object(self):
        runtime = Runtime()
        base = runtime.new_class(Mixin("Base"), None, "base-eo")
        source = runtime.new_class(Mixin("Shared"), base, "source-eo")
        applied = runtime.apply_mixin(base, "new", source, "new")
        self.assertIs(applied.mixin, source.mixin)
        self.assertEqual(applied.enclosing_object, "source-eo")
        self.assertIs(applied.superclass, base)

    def test_mixin_application_rejects_wrong_factory_selector(self):
        runtime = Runtime()
        base = runtime.new_class(Mixin("Base"), None, None, "with:", 1)
        source = runtime.new_class(Mixin("Shared"), base, None)
        with self.assertRaisesRegex(ValueError, "wrong superclass factory"):
            runtime.apply_mixin(base, "new", source, "new")

    def test_layout_and_initialization_are_root_to_leaf(self):
        runtime = Runtime()

        def init_a(rt, obj, application, _args):
            self.assertEqual(obj.slots, {(a.identity, "a"): None, (b.identity, "b"): None})
            obj.slots[(application.identity, "a")] = 1

        def init_b(rt, obj, application, _args):
            self.assertEqual(obj.slots[(a.identity, "a")], 1)
            obj.slots[(application.identity, "b")] = 2

        a = runtime.new_class(Mixin("A", ("a",), init_a), None, None)
        b = runtime.new_class(Mixin("B", ("b",), init_b), a, None)
        obj = runtime.new_instance(b)
        self.assertEqual(tuple(obj.slots), ((a.identity, "a"), (b.identity, "b")))
        self.assertEqual(obj.slots, {(a.identity, "a"): 1, (b.identity, "b"): 2})
        self.assertEqual(runtime.trace, ["init:A", "init:B"])

    def test_sequential_slots_observe_prior_writes(self):
        runtime = Runtime()
        cls = runtime.new_class(Mixin("M", ("a", "b")), None, None)
        obj = runtime.basic_new(cls)
        runtime.sequential_slots(
            obj, cls,
            (("a", lambda: 3), ("b", lambda: obj.slots[(cls.identity, "a")] + 4)),
        )
        self.assertEqual(obj.slots, {(cls.identity, "a"): 3, (cls.identity, "b"): 7})

    def test_simultaneous_slots_are_all_installed_before_resolution(self):
        runtime = Runtime()
        cls = runtime.new_class(Mixin("M", ("a", "b")), None, None)
        obj = runtime.basic_new(cls)

        def a_value():
            self.assertIsInstance(obj.slots[(cls.identity, "b")], PullFuture)
            return 1

        def b_value():
            self.assertIsInstance(obj.slots[(cls.identity, "a")], PullFuture)
            return 2

        runtime.simultaneous_slots(obj, cls, (("a", a_value), ("b", b_value)))
        self.assertEqual(runtime.trace, ["resolve:a", "resolve:b"])
        self.assertEqual(obj.slots[(cls.identity, "a")].resolve(), 1)
        self.assertEqual(obj.slots[(cls.identity, "b")].resolve(), 2)

    def test_lazy_nil_result_is_recomputed(self):
        runtime = Runtime()
        cls = runtime.new_class(Mixin("M", ("lazy",)), None, None)
        obj = runtime.basic_new(cls)
        calls = []

        def initializer():
            calls.append(1)
            return None

        self.assertIsNone(runtime.lazy_read(obj, cls, "lazy", initializer))
        self.assertIsNone(runtime.lazy_read(obj, cls, "lazy", initializer))
        self.assertEqual(len(calls), 2)

    def test_nested_class_cache_is_per_receiver(self):
        runtime = Runtime()
        outer = runtime.new_class(Mixin("Outer"), None, None)
        o1 = runtime.basic_new(outer)
        o2 = runtime.basic_new(outer)
        inner_mixin = Mixin("Inner")
        constructor = lambda eo: runtime.new_class(inner_mixin, outer, eo)
        c11 = runtime.nested_class(o1, outer, "InnerDecl", constructor)
        c12 = runtime.nested_class(o1, outer, "InnerDecl", constructor)
        c2 = runtime.nested_class(o2, outer, "InnerDecl", constructor)
        self.assertIs(c11, c12)
        self.assertIs(c11.enclosing_object, o1)
        self.assertIs(c2.enclosing_object, o2)
        self.assertNotEqual(c11.identity, c2.identity)

    def test_repeated_mixin_initializers_and_lazy_cells_are_independent(self):
        runtime = Runtime()
        def initialize(rt, obj, application, _args):
            rt.sequential_slots(obj, application, (("x", lambda: application.identity),))
        mixin = Mixin("Repeated", ("x", "lazy"), initialize)
        base = runtime.new_class(mixin, None, None)
        derived = runtime.new_class(mixin, base, None)
        obj = runtime.new_instance(derived)
        self.assertEqual(len(obj.slots), 4)
        self.assertEqual(obj.slots[(base.identity, "x")], base.identity)
        self.assertEqual(obj.slots[(derived.identity, "x")], derived.identity)
        self.assertEqual(runtime.lazy_read(obj, base, "lazy", lambda: 1), 1)
        self.assertEqual(runtime.lazy_read(obj, derived, "lazy", lambda: 2), 2)

    def test_repeated_mixin_nested_cache_is_independent(self):
        runtime = Runtime()
        mixin = Mixin("Repeated")
        base = runtime.new_class(mixin, None, None)
        derived = runtime.new_class(mixin, base, None)
        obj = runtime.basic_new(derived)
        constructor = lambda eo: runtime.new_class(Mixin("Inner"), base, eo)
        first = runtime.nested_class(obj, base, "N", constructor)
        second = runtime.nested_class(obj, derived, "N", constructor)
        self.assertIsNot(first, second)
        self.assertIs(first, runtime.nested_class(obj, base, "N", constructor))


if __name__ == "__main__":
    unittest.main()
