import unittest

from frontend_model import (
    Capture,
    Char,
    Choice,
    Empty,
    FrontEndImage,
    Grammar,
    InvalidGrammar,
    LanguageObject,
    Node,
    Ref,
    Sequence,
    Star,
    compile_unit,
    parse_complete,
    recognize,
    validate_grammar,
)


class PegTests(unittest.TestCase):
    def test_ordered_choice_restarts_at_original_offset(self):
        grammar = Grammar(
            "start",
            {
                "start": Capture(
                    "start",
                    Choice(Sequence(Char("a"), Char("b")), Char("a")),
                )
            },
        )
        tree = parse_complete(grammar, "a")
        self.assertEqual((tree.start, tree.end), (0, 1))

    def test_repetition_is_greedy_and_capture_retains_span(self):
        grammar = Grammar(
            "start", {"start": Capture("letters", Star(Char("a")))}
        )
        tree = parse_complete(grammar, "aaa")
        self.assertIsInstance(tree, Node)
        self.assertEqual((tree.start, tree.end, len(tree.children)), (0, 3, 3))

    def test_complete_parse_rejects_unconsumed_suffix(self):
        grammar = Grammar("start", {"start": Capture("one", Char("a"))})
        with self.assertRaises(ValueError):
            parse_complete(grammar, "ab")

    def test_nullable_repetition_is_invalid(self):
        grammar = Grammar("start", {"start": Capture("bad", Star(Empty()))})
        with self.assertRaises(InvalidGrammar):
            validate_grammar(grammar)

    def test_left_recursion_is_invalid(self):
        grammar = Grammar("start", {"start": Ref("start")})
        with self.assertRaises(InvalidGrammar):
            validate_grammar(grammar)


class _Parser:
    def __init__(self, tag, during=None):
        self.tag = tag
        self.during = during

    def parse_source(self, source):
        if self.during is not None:
            self.during()
        return (self.tag, source)


class _Elaborator:
    def __init__(self, tag):
        self.tag = tag

    def elaborate_surface(self, surface):
        return (self.tag, surface)


class _Compiler:
    def __init__(self, tag):
        self.tag = tag

    def compile_core(self, core):
        return (self.tag, core)


class FrontEndImageTests(unittest.TestCase):
    def make_language(self):
        return LanguageObject(
            _Parser("p0"), _Elaborator("e0"), _Compiler("c0"), "g0", 0
        )

    def compile(self, language):
        return compile_unit(
            language,
            "source",
            core_ok=lambda core: core[0].startswith("e"),
            artifact_ok=lambda artifact, core: artifact[1] == core,
        )

    def test_ordinary_component_replacement_affects_next_compilation(self):
        language = self.make_language()
        first = self.compile(language)
        language.parser = _Parser("p1")
        language.elaborator = _Elaborator("e1")
        language.compiler = _Compiler("c1")
        language.revision = 1
        second = self.compile(language)
        self.assertEqual(first.image.revision, 0)
        self.assertEqual(second.image.revision, 1)
        self.assertEqual(second.artifact[0], "c1")

    def test_current_compilation_keeps_its_captured_image(self):
        language = self.make_language()

        def replace_later_stages():
            language.elaborator = _Elaborator("e1")
            language.compiler = _Compiler("c1")
            language.revision = 1

        language.parser = _Parser("p0", replace_later_stages)
        current = self.compile(language)
        later = self.compile(language)
        self.assertEqual(current.core[0], "e0")
        self.assertEqual(current.artifact[0], "c0")
        self.assertEqual(later.core[0], "e1")
        self.assertEqual(later.artifact[0], "c1")

    def test_invalid_core_is_rejected_at_fixed_boundary(self):
        language = self.make_language()
        with self.assertRaises(ValueError):
            compile_unit(
                language,
                "source",
                core_ok=lambda core: False,
                artifact_ok=lambda artifact, core: True,
            )


if __name__ == "__main__":
    unittest.main()
