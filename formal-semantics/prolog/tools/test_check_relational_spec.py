import importlib.util
import sys
import unittest
from pathlib import Path


CHECKER_PATH = Path(__file__).with_name("check_relational_spec.py")
SPEC = importlib.util.spec_from_file_location("check_relational_spec", CHECKER_PATH)
assert SPEC and SPEC.loader
CHECKER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECKER
SPEC.loader.exec_module(CHECKER)


class RelationalSpecCheckerTests(unittest.TestCase):
    def test_nested_argument_splitting(self):
        self.assertEqual(
            CHECKER.split_top_level("P, some(pair(X, Y)), [A,B|Tail]"),
            ["P", "some(pair(X, Y))", "[A,B|Tail]"],
        )

    def test_signature(self):
        self.assertEqual(
            CHECKER.term_signature("lookup(P, H, some(result(F, C)))"),
            ("lookup", 3),
        )

    def test_secondary_latex_references_are_retained(self):
        clauses = CHECKER.clauses_from(
            "% @latex rule:One\n"
            "% @also equation:one, equation:two\n"
            "% @lean Newspeak.One\n"
            "% @mode one(+)\n"
            "one(X).\n"
        )
        self.assertEqual(
            clauses[0][1]["also"], "equation:one, equation:two"
        )

    def test_json_manifest_normalizes_secondary_references(self):
        root = CHECKER_PATH.parents[1]
        clauses, errors = CHECKER.check(root)
        self.assertFalse(errors, "\n".join(errors))
        payload = CHECKER.manifest_payload(root, clauses)
        self.assertTrue(all(isinstance(row["also"], list)
            for row in payload["clauses"]))

    def test_repository_source_passes(self):
        root = CHECKER_PATH.parents[1]
        clauses, errors = CHECKER.check(root)
        self.assertFalse(errors, "\n".join(errors))
        self.assertGreater(len(clauses), 20)

    def test_every_equation_has_a_checked_disposition(self):
        root = CHECKER_PATH.parents[1]
        equations, _rules = CHECKER.find_latex_references(root.parent)
        dispositions, errors = CHECKER.read_equation_dispositions(root)
        self.assertFalse(errors, "\n".join(errors))
        clauses, check_errors = CHECKER.check(root)
        self.assertFalse(check_errors, "\n".join(check_errors))
        encoded = {
            reference.removeprefix("equation:")
            for clause in clauses
            for reference in CHECKER.clause_latex_references(clause)
            if reference.startswith("equation:")
        }
        self.assertEqual(set(dispositions) | encoded, equations)


if __name__ == "__main__":
    unittest.main()
