import unittest
from pathlib import Path
import tempfile

from check_sources import ROOT, audit, latex_inventory, scan_source


class ProvenanceTests(unittest.TestCase):
    def test_all_sources_are_auditable(self):
        markdown, manifest = audit()
        self.assertIn("pending", markdown)
        self.assertIn('"origins"', manifest)

    def test_inventory_contains_actor_reflection_gc_and_frontend(self):
        inventory = latex_inventory(ROOT.parent / "newspeak-semantics.tex")
        files = {file for file, _ in inventory.values()}
        self.assertTrue({"actor-semantics.tex", "reflection-semantics.tex",
                         "gc-semantics.tex", "front-end-semantics.tex"} <= files)

    def check_bad(self, source, message):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.spectec"
            path.write_text(source)
            with self.assertRaisesRegex(ValueError, message):
                scan_source(path, {"eq:direct": ("spec.tex", 1), "U-Top": ("spec.tex", 2)})

    def test_unknown_origin(self):
        self.check_bad(";; @equation eq:typo\ndef $f(nat) : nat\n", "unknown LaTeX")

    def test_rule_annotation_requires_rule(self):
        self.check_bad(";; @rule U-Top\ndef $f(nat) : nat\n", "must annotate a rule")

    def test_orphan(self):
        self.check_bad(";; @equation eq:direct\n", "orphaned")

    def test_wrong_kind(self):
        self.check_bad(";; @rule eq:direct\nrule X/a: 0\n", "wrong origin kind")

    def test_partial_rule_is_auditable(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "partial.spectec"
            path.write_text(";; @partial U-Top\nrule X/a: 0\n")
            origins = scan_source(path, {"U-Top": ("spec.tex", 2)})
            self.assertEqual(origins[0].kind, "partial")

    def test_partial_rule_still_requires_rule(self):
        self.check_bad(";; @partial U-Top\ndef $f(nat) : nat\n", "must annotate a rule")


if __name__ == "__main__":
    unittest.main()
