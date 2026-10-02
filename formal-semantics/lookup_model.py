"""Executable oracle for the lookup fragment of newspeak-semantics.tex.

This is deliberately small and non-normative.  It exists to make distinctions
in the inference rules testable while the full reference machine is developed.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, Optional, Tuple


class Access(Enum):
    PUBLIC = "public"
    PROTECTED = "protected"
    PRIVATE = "private"


@dataclass(frozen=True)
class Method:
    selector: str
    access: Access
    owner_decl: str


@dataclass
class Class:
    name: str
    declaration: str
    superclass: Optional["Class"] = None
    methods: Dict[str, Method] = field(default_factory=dict)


LookupResult = Optional[Tuple[Method, Class]]


def lookup_unrestricted(selector: str, cls: Optional[Class]) -> LookupResult:
    """First direct definition, regardless of accessibility."""
    while cls is not None:
        method = cls.methods.get(selector)
        if method is not None:
            return method, cls
        cls = cls.superclass
    return None


def lookup_public(selector: str, cls: Optional[Class]) -> LookupResult:
    """Specification 5.5: protected blocks; private is transparent."""
    while cls is not None:
        method = cls.methods.get(selector)
        if method is None or method.access is Access.PRIVATE:
            cls = cls.superclass
            continue
        if method.access is Access.PUBLIC:
            return method, cls
        assert method.access is Access.PROTECTED
        return None
    return None


def lookup_protected(selector: str, cls: Optional[Class]) -> LookupResult:
    """Specification 5.9/5.10: public and protected are inherited."""
    while cls is not None:
        method = cls.methods.get(selector)
        if method is not None and method.access is not Access.PRIVATE:
            return method, cls
        cls = cls.superclass
    return None


def nearest_application(cls: Optional[Class], declaration: str) -> Optional[Class]:
    """Most-specific application of a declaration's mixin in a class chain."""
    while cls is not None:
        if cls.declaration == declaration:
            return cls
        cls = cls.superclass
    return None


def ordinary_dispatch(selector: str, receiver_class: Class) -> Tuple[str, Method, Class]:
    result = lookup_public(selector, receiver_class)
    if result is not None:
        return "invoke", result[0], result[1]
    dnu = lookup_unrestricted("doesNotUnderstand:", receiver_class)
    if dnu is None:
        raise LookupError("ill-formed base program: Object supplies no DNU")
    return "dnu", dnu[0], dnu[1]

def outer_dispatch(
    selector: str, receiver_class: Class, target_declaration: str
) -> Tuple[str, Method, Class]:
    """Dispatch after the enclosing receiver has already been selected."""
    target_class = nearest_application(receiver_class, target_declaration)
    if target_class is None:
        raise LookupError("outer target has no application in receiver class chain")
    lexical = target_class.methods.get(selector)
    if lexical is not None and lexical.access is Access.PRIVATE:
        return "invoke-private", lexical, target_class
    result = lookup_protected(selector, receiver_class)
    if result is not None:
        return "invoke", result[0], result[1]
    dnu = lookup_unrestricted("doesNotUnderstand:", receiver_class)
    if dnu is None:
        raise LookupError("ill-formed base program: Object supplies no DNU")
    return "dnu", dnu[0], dnu[1]


def super_dispatch(selector: str, current_class: Class) -> Tuple[str, Method, Class]:
    """Lookup and DNU both start above current_class; receiver stays self."""
    start = current_class.superclass
    if start is None:
        raise RuntimeError("super send from Object or Top")
    result = lookup_protected(selector, start)
    if result is not None:
        return "invoke", result[0], result[1]
    dnu = lookup_unrestricted("doesNotUnderstand:", start)
    if dnu is None:
        raise LookupError("ill-formed base program: Object supplies no DNU")
    return "dnu", dnu[0], dnu[1]
