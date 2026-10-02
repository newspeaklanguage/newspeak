import unittest

from actor_model import ActorWorld, Far, Message, Near, Value


class ActorModelTests(unittest.TestCase):
    def test_near_send_returns_promise_and_queues_later_turn(self):
        world = ActorWorld(("A",))
        promise = world.async_send("A", Near("A", "o"), Message("ping"))
        self.assertEqual(world.promises[promise].status, "pending")
        self.assertEqual(len(world.mailboxes["A"]), 1)
        self.assertEqual(world.mailboxes["A"][0].target, Near("A", "o"))

    def test_remote_representation_preserves_values_and_normalizes_home(self):
        world = ActorWorld(("A", "B", "C"))
        value = Value((1, 2))
        far = Far("B", "o")
        self.assertIs(world.remote_representation("A", "B", value), value)
        self.assertEqual(
            world.remote_representation("A", "B", far), Near("B", "o")
        )
        self.assertIs(world.remote_representation("A", "C", far), far)
        self.assertEqual(
            world.remote_representation("A", "B", Near("A", "x")),
            Far("A", "x"),
        )

    def test_remote_arguments_do_not_share_mutable_near_objects(self):
        world = ActorWorld(("A", "B"))
        world.async_send(
            "A",
            Far("B", "target"),
            Message("take:", (Near("A", "mutable"), Value(3))),
        )
        packet = world.network[0]
        self.assertEqual(packet.message.arguments, (Far("A", "mutable"), Value(3)))

    def test_two_sends_from_one_actor_obey_e_order(self):
        world = ActorWorld(("A", "B"))
        world.async_send("A", Far("B", "o"), Message("first"))
        world.async_send("A", Far("B", "o"), Message("second"))
        first, second = world.network
        self.assertFalse(world.eligible(second))
        with self.assertRaisesRegex(ValueError, "E-order"):
            world.deliver(second)
        world.deliver(first)
        self.assertTrue(world.eligible(second))
        world.deliver(second)
        self.assertEqual(
            [packet.message.selector for packet in world.mailboxes["B"]],
            ["first", "second"],
        )

    def test_passing_far_reference_carries_prior_send_barrier(self):
        world = ActorWorld(("A", "B", "C"))
        far_b = Far("B", "o")
        world.async_send("A", far_b, Message("first"))
        world.async_send("A", Far("C", "c"), Message("take:", (far_b,)))
        first, handoff = world.network
        world.deliver(handoff)
        received = world.dequeue("C")
        passed_far = received.message.arguments[0]
        world.async_send("C", passed_far, Message("afterHandoff"))
        successor = next(p for p in world.network if p.message.selector == "afterHandoff")
        self.assertFalse(world.eligible(successor))
        world.deliver(first)
        self.assertTrue(world.eligible(successor))

    def test_send_to_pending_promise_routes_after_fulfillment(self):
        world = ActorWorld(("A", "B"))
        base = world.async_send("A", Far("B", "maker"), Message("make"))
        dependent = world.async_send("A", base, Message("use"))
        self.assertEqual(len(world.promises[base].waiters), 1)
        self.assertFalse(any(p.message.selector == "use" for p in world.network))
        world.settle(base, "fulfilled", "B", Near("B", "made"))
        use = next(p for p in world.network if p.message.selector == "use")
        self.assertEqual(use.reply, dependent)
        self.assertEqual(use.target, Near("B", "made"))

    def test_send_to_broken_promise_propagates_break(self):
        world = ActorWorld(("A",))
        base = world.async_send("A", Near("A", "o"), Message("fail"))
        world.settle(base, "broken", "A", Value("boom"))
        dependent = world.async_send("A", base, Message("never"))
        self.assertEqual(world.promises[dependent].status, "broken")
        self.assertEqual(world.promises[dependent].result, Value("boom"))

    def test_promise_settles_at_most_once(self):
        world = ActorWorld(("A",))
        promise = world.async_send("A", Near("A", "o"), Message("once"))
        world.settle(promise, "fulfilled", "A", Value(1))
        with self.assertRaisesRegex(ValueError, "already settled"):
            world.settle(promise, "broken", "A", Value("late"))


if __name__ == "__main__":
    unittest.main()
