import unittest

from debugger_model import (
    Activation,
    ActorState,
    Control,
    DebuggerError,
    DebuggerVM,
    FrameTemplate,
    copy_stack_frame_segment,
    fresh_key,
    image_stack,
    materialize_stack_template,
    pop_stack_frames,
    push_stack_frame,
    retain_key,
)


class DebuggerModelTests(unittest.TestCase):
    def setUp(self):
        self.heap = {
            "a0": Activation("method:outer", None, "a0"),
            "a1": Activation("method:inner", "a0", "a1"),
            "a2": Activation("method:debugger", "a1", "a2"),
        }

    def test_stack_image_gives_every_frame_a_current_term(self):
        image = image_stack(("a0", "a1"), "send:signal", self.heap, {"a0": ("seq",)})
        self.assertIsNone(image[0].control.term)
        self.assertEqual(image[1].control.term, "send:signal")

    def test_pop_promotes_selected_frame_with_chosen_value(self):
        image = image_stack(("a0", "a1", "a2"), "debugger", self.heap, {})
        resumed = pop_stack_frames(image, 2, "resume-value")
        self.assertEqual(len(resumed), 1)
        self.assertEqual(resumed[0].control.term, "resume-value")

    def test_push_demotes_old_top_and_activates_new_top(self):
        image = image_stack(("a0",), "old-term", self.heap, {})
        pushed = FrameTemplate(
            fresh_key("new"), Activation("method:new", retain_key("a0"), None), Control.running("new-term")
        )
        result = push_stack_frame(image, pushed)
        self.assertFalse(result[0].control.active)
        self.assertEqual(result[1].control.term, "new-term")

    def test_copy_segment_uses_fresh_keys_and_rewires_internal_links(self):
        image = image_stack(("a0", "a1"), "inner", self.heap, {})
        image[1].record.continuation = retain_key("a0")
        image[1].record.home = retain_key("a1")
        image[1].record.lexical_environment = {"outer": retain_key("a0")}
        copied = copy_stack_frame_segment(image, 0, 1, ("c0", "c1"))
        self.assertEqual(copied[0].key, fresh_key("c0"))
        self.assertEqual(copied[1].record.continuation, fresh_key("c0"))
        self.assertEqual(copied[1].record.home, fresh_key("c1"))
        self.assertEqual(copied[1].record.lexical_environment["outer"], fresh_key("c0"))

    def test_materialization_is_atomic_and_retires_removed_frames(self):
        image = image_stack(("a0", "a1"), "inner", self.heap, {})
        resumed = pop_stack_frames(image, 1, "result")
        candidate, stack, term = materialize_stack_template(
            self.heap, ("a0", "a1"), resumed, lambda: "fresh"
        )
        self.assertEqual(stack, ("a0",))
        self.assertEqual(term, "result")
        self.assertFalse(candidate["a1"].continuable)
        self.assertTrue(self.heap["a1"].continuable)

    def test_invalid_install_does_not_change_live_vm(self):
        vm = DebuggerVM(
            self.heap,
            {"actor": ActorState("running", ("a0", "a1"), "inner")},
        )
        token = vm.pause_actor("debugger", "actor", "breakpoint")
        bad = (
            FrameTemplate(retain_key("a0"), self.heap["a0"], Control.running("bad-lower")),
            FrameTemplate(retain_key("a1"), self.heap["a1"], Control.running("bad-top")),
        )
        before_heap = vm.heap.copy()
        before_state = vm.actors["actor"]
        with self.assertRaises(DebuggerError):
            vm.replace_paused_stack("actor", token, bad)
        self.assertEqual(vm.heap, before_heap)
        self.assertEqual(vm.actors["actor"], before_state)

    def test_paused_edit_invalidates_old_token_and_full_speed_resumes(self):
        vm = DebuggerVM(
            self.heap,
            {"actor": ActorState("running", ("a0", "a1"), "inner")},
        )
        token = vm.pause_actor("debugger", "actor", "exception")
        image = image_stack(("a0", "a1"), "inner", vm.heap, {})
        next_token = vm.replace_paused_stack("actor", token, image)
        with self.assertRaises(DebuggerError):
            vm.resume_paused_actor_at_full_speed("actor", token)
        vm.resume_paused_actor_at_full_speed("actor", next_token)
        self.assertEqual(vm.actors["actor"].mode, "running")
        self.assertEqual(vm.actors["actor"].term, "inner")

    def test_running_stack_replacement_is_self_only(self):
        vm = DebuggerVM(
            self.heap,
            {"target": ActorState("running", ("a0", "a1"), "inner")},
        )
        image = image_stack(("a0", "a1"), "inner", vm.heap, {})
        with self.assertRaises(DebuggerError):
            vm.replace_current_actor_stack("other", "target", image)
        vm.replace_current_actor_stack("target", "target", image)


if __name__ == "__main__":
    unittest.main()
