"""Small executable oracle for the optional garbage-collection layer.

The LaTeX semantics remains normative.  This model pins down strong and
ephemeron reachability, WeakArray clearing, WeakMap key/value behavior, closed
partial collection, and permanent non-reuse of collected identities.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Mapping


Ref = str


@dataclass(frozen=True)
class GCState:
    records: Mapping[Ref, frozenset[Ref]]
    roots: frozenset[Ref]
    classes: Mapping[Ref, str]
    used: frozenset[Ref]
    mixins: Mapping[Ref, str] = field(default_factory=dict)
    weak_arrays: Mapping[Ref, tuple[Ref | None, ...]] = field(default_factory=dict)
    weak_maps: Mapping[Ref, Mapping[Ref, Ref | None]] = field(default_factory=dict)

    def __post_init__(self) -> None:
        domain = set(self.records)
        if not domain <= set(self.used):
            raise ValueError("every resident reference must occur in allocation history")
        if not set(self.roots) <= domain:
            raise ValueError("every root must resolve in the reference store")
        if not set(self.classes) <= domain:
            raise ValueError("class metadata may describe only resident references")
        if not set(self.mixins) <= domain:
            raise ValueError("mixin metadata may describe only resident class references")
        if not set(self.weak_arrays) <= domain:
            raise ValueError("weak-array metadata may describe only resident references")
        if not set(self.weak_maps) <= domain:
            raise ValueError("weak-map metadata may describe only resident references")
        for successors in self.records.values():
            if not set(successors) <= domain:
                raise ValueError("resident records may not contain dangling strong edges")
        for cells in self.weak_arrays.values():
            if not {cell for cell in cells if cell is not None} <= domain:
                raise ValueError("weak-array cells must initially resolve")
        for entries in self.weak_maps.values():
            if not set(entries) <= domain:
                raise ValueError("weak-map keys must initially resolve")
            if not {value for value in entries.values() if value is not None} <= domain:
                raise ValueError("weak-map values must initially resolve")


def reachable_references(state: GCState) -> frozenset[Ref]:
    reached = set(state.roots)
    changed = True
    while changed:
        changed = False
        for source in tuple(reached):
            for target in state.records[source]:
                if target not in reached:
                    reached.add(target)
                    changed = True
            for key, value in state.weak_maps.get(source, {}).items():
                if key in reached and value is not None and value not in reached:
                    reached.add(value)
                    changed = True
    return frozenset(reached)


def garbage_references(state: GCState) -> frozenset[Ref]:
    return frozenset(set(state.records) - set(reachable_references(state)))


def admissible_collection(state: GCState, selected: frozenset[Ref]) -> bool:
    if not selected or not set(selected) <= set(garbage_references(state)):
        return False
    retained = set(state.records) - set(selected)
    return all(not (set(state.records[source]) & set(selected)) for source in retained)


def collect_references(state: GCState, selected: frozenset[Ref]) -> GCState:
    if not admissible_collection(state, selected):
        raise ValueError("selected records are not an admissible closed garbage set")
    records = {
        source: successors
        for source, successors in state.records.items()
        if source not in selected
    }
    classes = {
        reference: class_name
        for reference, class_name in state.classes.items()
        if reference not in selected
    }
    mixins = {
        reference: mixin_name
        for reference, mixin_name in state.mixins.items()
        if reference not in selected
    }
    weak_arrays = {
        owner: tuple(None if cell in selected else cell for cell in cells)
        for owner, cells in state.weak_arrays.items()
        if owner not in selected
    }
    weak_maps = {
        owner: {
            key: value
            for key, value in entries.items()
            if key not in selected and value not in selected
        }
        for owner, entries in state.weak_maps.items()
        if owner not in selected
    }
    return GCState(
        records,
        state.roots,
        classes,
        state.used,
        mixins,
        weak_arrays,
        weak_maps,
    )


def allocate_reference(
    state: GCState,
    reference: Ref,
    successors: frozenset[Ref] = frozenset(),
    class_name: str | None = None,
    mixin_name: str | None = None,
) -> GCState:
    if reference in state.used:
        raise ValueError("reference identity has already been used")
    if not set(successors) <= set(state.records):
        raise ValueError("a new record may point only to resident references")
    records = dict(state.records)
    records[reference] = successors
    classes = dict(state.classes)
    if class_name is not None:
        classes[reference] = class_name
    mixins = dict(state.mixins)
    if mixin_name is not None:
        mixins[reference] = mixin_name
    return GCState(
        records,
        state.roots,
        classes,
        state.used | {reference},
        mixins,
        state.weak_arrays,
        state.weak_maps,
    )


def allocate_weak_array(state: GCState, reference: Ref, size: int) -> GCState:
    if size < 0:
        raise ValueError("weak-array size must be nonnegative")
    allocated = allocate_reference(state, reference, class_name="WeakArray")
    weak_arrays = dict(allocated.weak_arrays)
    weak_arrays[reference] = (None,) * size
    return replace(allocated, weak_arrays=weak_arrays)


def weak_array_read(state: GCState, array: Ref, index: int) -> Ref | None:
    return state.weak_arrays[array][index]


def write_weak_array_cell(
    state: GCState, array: Ref, index: int, value: Ref | None
) -> GCState:
    if value is not None and value not in state.records:
        raise ValueError("weak-array value must resolve")
    cells = list(state.weak_arrays[array])
    cells[index] = value
    weak_arrays = dict(state.weak_arrays)
    weak_arrays[array] = tuple(cells)
    return replace(state, weak_arrays=weak_arrays)


def allocate_weak_map(state: GCState, reference: Ref) -> GCState:
    allocated = allocate_reference(state, reference, class_name="WeakMap")
    weak_maps = dict(allocated.weak_maps)
    weak_maps[reference] = {}
    return replace(allocated, weak_maps=weak_maps)


def weak_map_lookup(state: GCState, weak_map: Ref, key: Ref) -> Ref | None:
    return state.weak_maps[weak_map].get(key)


def write_weak_map_entry(
    state: GCState, weak_map: Ref, key: Ref, value: Ref | None
) -> GCState:
    if key not in state.records:
        raise ValueError("weak-map key must resolve")
    if value is not None and value not in state.records:
        raise ValueError("weak-map value must resolve")
    weak_maps = {owner: dict(entries) for owner, entries in state.weak_maps.items()}
    weak_maps[weak_map][key] = value
    return replace(state, weak_maps=weak_maps)


def exact_instances(state: GCState, class_name: str) -> tuple[Ref, ...]:
    return tuple(
        sorted(reference for reference, cls in state.classes.items() if cls == class_name)
    )


def mixin_applications(state: GCState, mixin_name: str) -> tuple[Ref, ...]:
    return tuple(
        sorted(
            reference
            for reference, mixin in state.mixins.items()
            if mixin == mixin_name
        )
    )
