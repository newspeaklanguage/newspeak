"""Guard the review-facing declaration/storage distinction in the reference."""

import unittest

import generate_reference as reference


class DeclarationStorageReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.entries = reference.build_entries()
        cls.by_id = {entry["sourceId"]: entry for entry in cls.entries}

    def test_own_slots_is_numbered_and_all_components_are_described(self):
        entry = self.by_id["eq:own-slots"]
        self.assertNotEqual(entry["number"], "—")
        descriptions = {p["notation"]: p["description"] for p in entry["parameters"]}
        self.assertEqual(set(descriptions), {
            "P", "M", "d_j", "j", "K", "\\phi", "\\delta", "\\nu", "\\iota",
        })
        self.assertIn("Static", descriptions["\\delta"])
        self.assertIn("not runtime cells", descriptions["\\delta"])
        self.assertIn("every application", descriptions["j"])

    def test_static_projection_and_runtime_layout_are_linked_both_ways(self):
        own = self.by_id["eq:own-slots"]
        layout = self.by_id["eq:slot-layout"]
        self.assertIn(layout["id"], {r["id"] for r in own["relatedDefinitions"]})
        self.assertIn(own["id"], {r["id"] for r in layout["relatedDefinitions"]})

    def test_equations_have_unique_anchors_and_resolved_numbers(self):
        self.assertEqual(len(self.entries), len({e["id"] for e in self.entries}))
        for entry in self.entries:
            if entry["kind"] != "Rule":
                self.assertNotEqual(entry["number"], "—", entry["sourceId"])

    def test_array_padding_is_removed_without_changing_equation_content(self):
        source = r"\begin{array}{@{}rcl@{}}x&=&y\end{array}"
        self.assertEqual(reference.clean_formula(source),
                         r"\begin{array}{rcl}x&=&y\end{array}")

    def test_stretchable_tex_spacing_has_a_browser_equivalent(self):
        self.assertEqual(reference.clean_formula(r"x\hfill\text{if }p"),
                         r"x\qquad\text{if }p")


if __name__ == "__main__":
    unittest.main()
