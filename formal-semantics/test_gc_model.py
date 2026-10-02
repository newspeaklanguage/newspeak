import unittest

from gc_model import (
    GCState,
    admissible_collection,
    allocate_weak_array,
    allocate_weak_map,
    allocate_reference,
    collect_references,
    exact_instances,
    garbage_references,
    mixin_applications,
    reachable_references,
    weak_array_read,
    weak_map_lookup,
    write_weak_array_cell,
    write_weak_map_entry,
)


class GarbageCollectionModelTests(unittest.TestCase):
    def test_unreachable_cycle_is_garbage(self):
        state = GCState(
            records={"root": frozenset(), "a": frozenset({"b"}), "b": frozenset({"a"})},
            roots=frozenset({"root"}),
            classes={"a": "C", "b": "C"},
            used=frozenset({"root", "a", "b"}),
        )
        self.assertEqual(reachable_references(state), frozenset({"root"}))
        self.assertEqual(garbage_references(state), frozenset({"a", "b"}))

    def test_live_far_handle_retains_its_target(self):
        state = GCState(
            records={"far": frozenset({"target"}), "target": frozenset()},
            roots=frozenset({"far"}),
            classes={"target": "C"},
            used=frozenset({"far", "target"}),
        )
        self.assertEqual(reachable_references(state), frozenset({"far", "target"}))
        self.assertEqual(garbage_references(state), frozenset())

    def test_partial_collection_must_not_leave_dangling_edge(self):
        state = GCState(
            records={"a": frozenset({"b"}), "b": frozenset()},
            roots=frozenset(),
            classes={"a": "C", "b": "C"},
            used=frozenset({"a", "b"}),
        )
        self.assertFalse(admissible_collection(state, frozenset({"b"})))
        self.assertTrue(admissible_collection(state, frozenset({"a"})))
        self.assertTrue(admissible_collection(state, frozenset({"a", "b"})))

    def test_uncollected_garbage_remains_visible_to_instance_query(self):
        state = GCState(
            records={"old": frozenset(), "kept": frozenset()},
            roots=frozenset(),
            classes={"old": "C", "kept": "C"},
            used=frozenset({"old", "kept"}),
        )
        after = collect_references(state, frozenset({"old"}))
        self.assertEqual(exact_instances(state, "C"), ("kept", "old"))
        self.assertEqual(exact_instances(after, "C"), ("kept",))

    def test_collected_identity_is_never_reused(self):
        state = GCState(
            records={"old": frozenset()},
            roots=frozenset(),
            classes={"old": "C"},
            used=frozenset({"old"}),
        )
        after = collect_references(state, frozenset({"old"}))
        with self.assertRaises(ValueError):
            allocate_reference(after, "old", class_name="C")
        allocated = allocate_reference(after, "new", class_name="C")
        self.assertEqual(exact_instances(allocated, "C"), ("new",))

    def test_uncollected_mixin_application_remains_visible(self):
        state = GCState(
            records={"class-1": frozenset(), "class-2": frozenset()},
            roots=frozenset(),
            classes={},
            used=frozenset({"class-1", "class-2"}),
            mixins={"class-1": "M", "class-2": "M"},
        )
        after = collect_references(state, frozenset({"class-1"}))
        self.assertEqual(mixin_applications(state, "M"), ("class-1", "class-2"))
        self.assertEqual(mixin_applications(after, "M"), ("class-2",))

    def test_weak_array_does_not_retain_and_collected_cell_becomes_nil(self):
        state = GCState(
            records={"array": frozenset(), "target": frozenset()},
            roots=frozenset({"array"}),
            classes={},
            used=frozenset({"array", "target"}),
            weak_arrays={"array": ("target",)},
        )
        self.assertEqual(reachable_references(state), frozenset({"array"}))
        after = collect_references(state, frozenset({"target"}))
        self.assertIsNone(weak_array_read(after, "array", 0))

    def test_weak_array_preserves_strongly_reachable_element(self):
        state = GCState(
            records={"array": frozenset(), "target": frozenset()},
            roots=frozenset({"array", "target"}),
            classes={},
            used=frozenset({"array", "target"}),
            weak_arrays={"array": ("target",)},
        )
        self.assertEqual(garbage_references(state), frozenset())
        with self.assertRaises(ValueError):
            collect_references(state, frozenset({"target"}))

    def test_weak_map_value_is_conditionally_strong_when_key_is_live(self):
        state = GCState(
            records={
                "map": frozenset(),
                "key": frozenset(),
                "value": frozenset(),
            },
            roots=frozenset({"map", "key"}),
            classes={},
            used=frozenset({"map", "key", "value"}),
            weak_maps={"map": {"key": "value"}},
        )
        self.assertEqual(
            reachable_references(state), frozenset({"map", "key", "value"})
        )

    def test_weak_map_does_not_retain_key_or_value_without_live_key(self):
        state = GCState(
            records={
                "map": frozenset(),
                "key": frozenset(),
                "value": frozenset({"key"}),
            },
            roots=frozenset({"map"}),
            classes={},
            used=frozenset({"map", "key", "value"}),
            weak_maps={"map": {"key": "value"}},
        )
        self.assertEqual(reachable_references(state), frozenset({"map"}))
        after = collect_references(state, frozenset({"key", "value"}))
        self.assertIsNone(weak_map_lookup(after, "map", "key"))

    def test_partial_collection_clears_inactive_entry_value(self):
        state = GCState(
            records={
                "map": frozenset(),
                "key": frozenset(),
                "value": frozenset(),
            },
            roots=frozenset({"map"}),
            classes={},
            used=frozenset({"map", "key", "value"}),
            weak_maps={"map": {"key": "value"}},
        )
        after = collect_references(state, frozenset({"value"}))
        self.assertIn("key", after.records)
        self.assertIsNone(weak_map_lookup(after, "map", "key"))

    def test_weak_container_constructors_and_writes_preserve_contract(self):
        state = GCState(
            records={"key": frozenset(), "value": frozenset()},
            roots=frozenset(),
            classes={},
            used=frozenset({"key", "value"}),
        )
        state = allocate_weak_array(state, "array", 1)
        state = write_weak_array_cell(state, "array", 0, "value")
        state = allocate_weak_map(state, "map")
        state = write_weak_map_entry(state, "map", "key", "value")
        self.assertEqual(weak_array_read(state, "array", 0), "value")
        self.assertEqual(weak_map_lookup(state, "map", "key"), "value")


if __name__ == "__main__":
    unittest.main()
