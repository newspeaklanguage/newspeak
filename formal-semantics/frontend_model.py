"""Executable oracle for PEG recognition and reified front-end staging.

This is non-normative.  It pins down Equations 13.1--13.28 of the semantics:
PEG ordered choice, greedy repetition, capture spans, grammar admissibility,
complete-input recognition, one captured front-end image per compilation, and
ordinary replacement of parser/elaborator/compiler objects.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Mapping, Protocol


class PegExpression:
    pass


@dataclass(frozen=True)
class Empty(PegExpression):
    pass


@dataclass(frozen=True)
class Char(PegExpression):
    value: str


@dataclass(frozen=True)
class CharSet(PegExpression):
    values: frozenset[str]


@dataclass(frozen=True)
class AnyChar(PegExpression):
    pass


@dataclass(frozen=True)
class Ref(PegExpression):
    name: str


@dataclass(frozen=True)
class Sequence(PegExpression):
    first: PegExpression
    second: PegExpression


@dataclass(frozen=True)
class Choice(PegExpression):
    first: PegExpression
    second: PegExpression


@dataclass(frozen=True)
class Star(PegExpression):
    body: PegExpression


@dataclass(frozen=True)
class Not(PegExpression):
    body: PegExpression


@dataclass(frozen=True)
class And(PegExpression):
    body: PegExpression


@dataclass(frozen=True)
class Capture(PegExpression):
    name: str
    body: PegExpression


@dataclass(frozen=True)
class Leaf:
    start: int
    end: int


@dataclass(frozen=True)
class Node:
    name: str
    start: int
    end: int
    children: tuple[Leaf | "Node", ...]


Tree = Leaf | Node


@dataclass(frozen=True)
class Success:
    end: int
    forest: tuple[Tree, ...]


@dataclass(frozen=True)
class Failure:
    offset: int


Recognition = Success | Failure


@dataclass(frozen=True)
class Grammar:
    start: str
    productions: Mapping[str, PegExpression]


class InvalidGrammar(ValueError):
    pass


def _nullable(expr: PegExpression, nullable_names: frozenset[str]) -> bool:
    if isinstance(expr, Empty):
        return True
    if isinstance(expr, (Char, CharSet, AnyChar)):
        return False
    if isinstance(expr, Ref):
        return expr.name in nullable_names
    if isinstance(expr, Sequence):
        return _nullable(expr.first, nullable_names) and _nullable(
            expr.second, nullable_names
        )
    if isinstance(expr, Choice):
        return _nullable(expr.first, nullable_names) or _nullable(
            expr.second, nullable_names
        )
    if isinstance(expr, (Star, Not, And)):
        return True
    if isinstance(expr, Capture):
        return _nullable(expr.body, nullable_names)
    raise TypeError(expr)


def _referenced_names(expr: PegExpression) -> frozenset[str]:
    if isinstance(expr, Ref):
        return frozenset({expr.name})
    if isinstance(expr, (Sequence, Choice)):
        return _referenced_names(expr.first) | _referenced_names(expr.second)
    if isinstance(expr, (Star, Not, And, Capture)):
        return _referenced_names(expr.body)
    return frozenset()


def _star_bodies(expr: PegExpression) -> tuple[PegExpression, ...]:
    if isinstance(expr, Star):
        return (expr.body,) + _star_bodies(expr.body)
    if isinstance(expr, (Sequence, Choice)):
        return _star_bodies(expr.first) + _star_bodies(expr.second)
    if isinstance(expr, (Not, And, Capture)):
        return _star_bodies(expr.body)
    return ()


def _leading_names(
    expr: PegExpression, nullable_names: frozenset[str]
) -> frozenset[str]:
    if isinstance(expr, Ref):
        return frozenset({expr.name})
    if isinstance(expr, Sequence):
        names = _leading_names(expr.first, nullable_names)
        if _nullable(expr.first, nullable_names):
            names |= _leading_names(expr.second, nullable_names)
        return names
    if isinstance(expr, Choice):
        return _leading_names(expr.first, nullable_names) | _leading_names(
            expr.second, nullable_names
        )
    if isinstance(expr, (Star, Not, And, Capture)):
        return _leading_names(expr.body, nullable_names)
    return frozenset()


def validate_grammar(grammar: Grammar) -> None:
    names = frozenset(grammar.productions)
    if grammar.start not in names:
        raise InvalidGrammar("undefined start symbol")
    referenced = frozenset().union(
        *(_referenced_names(expr) for expr in grammar.productions.values())
    )
    if not referenced <= names:
        raise InvalidGrammar(f"undefined nonterminals: {sorted(referenced - names)}")

    nullable: frozenset[str] = frozenset()
    while True:
        grown = nullable | frozenset(
            name
            for name, expr in grammar.productions.items()
            if _nullable(expr, nullable)
        )
        if grown == nullable:
            break
        nullable = grown

    for expr in grammar.productions.values():
        for body in _star_bodies(expr):
            if _nullable(body, nullable):
                raise InvalidGrammar("nullable repetition body")

    graph = {
        name: _leading_names(expr, nullable)
        for name, expr in grammar.productions.items()
    }

    def visit(origin: str, current: str, seen: frozenset[str]) -> None:
        for successor in graph[current]:
            if successor == origin:
                raise InvalidGrammar("left-recursive nonterminal cycle")
            if successor not in seen:
                visit(origin, successor, seen | frozenset({successor}))

    for name in names:
        visit(name, name, frozenset({name}))


def recognize(
    grammar: Grammar, expression: PegExpression, source: str, offset: int
) -> Recognition:
    if isinstance(expression, Empty):
        return Success(offset, ())
    if isinstance(expression, Char):
        if offset < len(source) and source[offset] == expression.value:
            return Success(offset + 1, (Leaf(offset, offset + 1),))
        return Failure(offset)
    if isinstance(expression, CharSet):
        if offset < len(source) and source[offset] in expression.values:
            return Success(offset + 1, (Leaf(offset, offset + 1),))
        return Failure(offset)
    if isinstance(expression, AnyChar):
        if offset < len(source):
            return Success(offset + 1, (Leaf(offset, offset + 1),))
        return Failure(offset)
    if isinstance(expression, Ref):
        return recognize(grammar, grammar.productions[expression.name], source, offset)
    if isinstance(expression, Sequence):
        first = recognize(grammar, expression.first, source, offset)
        if isinstance(first, Failure):
            return first
        second = recognize(grammar, expression.second, source, first.end)
        if isinstance(second, Failure):
            return second
        return Success(second.end, first.forest + second.forest)
    if isinstance(expression, Choice):
        first = recognize(grammar, expression.first, source, offset)
        if isinstance(first, Success):
            return first
        return recognize(grammar, expression.second, source, offset)
    if isinstance(expression, Star):
        end = offset
        forest: tuple[Tree, ...] = ()
        while True:
            item = recognize(grammar, expression.body, source, end)
            if isinstance(item, Failure):
                return Success(end, forest)
            if item.end == end:
                raise InvalidGrammar("repetition made no progress")
            end = item.end
            forest += item.forest
    if isinstance(expression, Not):
        item = recognize(grammar, expression.body, source, offset)
        return Success(offset, ()) if isinstance(item, Failure) else Failure(offset)
    if isinstance(expression, And):
        item = recognize(grammar, expression.body, source, offset)
        return Success(offset, ()) if isinstance(item, Success) else Failure(offset)
    if isinstance(expression, Capture):
        item = recognize(grammar, expression.body, source, offset)
        if isinstance(item, Failure):
            return item
        return Success(
            item.end, (Node(expression.name, offset, item.end, item.forest),)
        )
    raise TypeError(expression)


def parse_complete(grammar: Grammar, source: str) -> Node:
    validate_grammar(grammar)
    result = recognize(grammar, Ref(grammar.start), source, 0)
    if not isinstance(result, Success) or result.end != len(source):
        raise ValueError("source is not a complete grammar match")
    if len(result.forest) != 1 or not isinstance(result.forest[0], Node):
        raise ValueError("start production must return one captured node")
    return result.forest[0]


class ParserService(Protocol):
    def parse_source(self, source: str) -> Any: ...


class ElaboratorService(Protocol):
    def elaborate_surface(self, surface: Any) -> Any: ...


class CompilerService(Protocol):
    def compile_core(self, core: Any) -> Any: ...


@dataclass(frozen=True)
class FrontEndImage:
    parser: ParserService
    elaborator: ElaboratorService
    compiler: CompilerService
    grammar: Any
    revision: Any


@dataclass
class LanguageObject:
    """An ordinary mutable object standing in for the Newspeak descriptor."""

    parser: ParserService
    elaborator: ElaboratorService
    compiler: CompilerService
    grammar: Any
    revision: Any

    def front_end_image(self) -> FrontEndImage:
        return FrontEndImage(
            self.parser,
            self.elaborator,
            self.compiler,
            self.grammar,
            self.revision,
        )


@dataclass(frozen=True)
class CompilationResult:
    surface: Any
    core: Any
    artifact: Any
    image: FrontEndImage


def compile_unit(
    language: LanguageObject,
    source: str,
    *,
    core_ok: Callable[[Any], bool],
    artifact_ok: Callable[[Any, Any], bool],
) -> CompilationResult:
    image = language.front_end_image()
    surface = image.parser.parse_source(source)
    core = image.elaborator.elaborate_surface(surface)
    if not core_ok(core):
        raise ValueError("elaborator returned an invalid annotated core")
    artifact = image.compiler.compile_core(core)
    if not artifact_ok(artifact, core):
        raise ValueError("compiler returned an invalid artifact")
    return CompilationResult(surface, core, artifact, image)
