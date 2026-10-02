"""Executable oracle for the debugger stack-image equations.

This model is deliberately small, but it is not a substitute semantics.  It
pins down the identity, control-shape, pause-token, and atomic-install details
that are easiest to get subtly wrong in an implementation of the LaTeX rules.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field, replace
from typing import Dict, Iterable, Optional, Tuple


class DebuggerError(ValueError):
    pass


@dataclass(frozen=True)
class Control:
    frames: Tuple[str, ...] = ()
    term: Optional[str] = None

    @property
    def active(self) -> bool:
        return self.term is not None

    @staticmethod
    def suspended(frames: Iterable[str] = ()) -> "Control":
        return Control(tuple(frames), None)

    @staticmethod
    def running(term: str, frames: Iterable[str] = ()) -> "Control":
        return Control(tuple(frames), term)


@dataclass
class Activation:
    provenance: str
    continuation: Optional[str]
    home: Optional[str]
    parameters: Dict[str, object] = field(default_factory=dict)
    locals: Dict[str, object] = field(default_factory=dict)
    lexical_environment: Dict[str, str] = field(default_factory=dict)
    continuable: bool = True


@dataclass
class FrameTemplate:
    # Retained keys are written "retain:<activation>".  Fresh keys are
    # template-local names written "fresh:<name>".
    key: str
    record: Activation
    control: Control


@dataclass
class ActorState:
    mode: str  # running, paused, or idle
    stack: Tuple[str, ...] = ()
    term: Optional[str] = None
    reply_promise: Optional[str] = None
    event: Optional[str] = None
    pause_token: Optional[str] = None
    stop_reason: Optional[str] = None


def retain_key(activation: str) -> str:
    return f"retain:{activation}"


def fresh_key(name: str) -> str:
    return f"fresh:{name}"


def image_stack(
    stack: Tuple[str, ...], term: str, heap: Dict[str, Activation], frames: Dict[str, Tuple[str, ...]]
) -> Tuple[FrameTemplate, ...]:
    if not stack:
        raise DebuggerError("an empty stack has no frame image")
    result = []
    for index, activation in enumerate(stack):
        if activation not in heap:
            raise DebuggerError(f"missing activation {activation}")
        control = (
            Control.running(term, frames.get(activation, ()))
            if index == len(stack) - 1
            else Control.suspended(frames.get(activation, ()))
        )
        result.append(FrameTemplate(retain_key(activation), deepcopy(heap[activation]), control))
    return tuple(result)


def pop_stack_frames(
    template: Tuple[FrameTemplate, ...], count: int, value: str
) -> Tuple[FrameTemplate, ...]:
    if count < 0 or count >= len(template):
        raise DebuggerError("pop must leave one frame")
    kept = list(deepcopy(template[:-count] if count else template))
    top = kept[-1]
    if top.control.active and count:
        raise DebuggerError("the promoted frame must have been suspended")
    kept[-1] = replace(top, control=Control.running(value, top.control.frames))
    return tuple(kept)


def push_stack_frame(
    template: Tuple[FrameTemplate, ...], frame: FrameTemplate
) -> Tuple[FrameTemplate, ...]:
    if not template or not template[-1].control.active or not frame.control.active:
        raise DebuggerError("push requires active old and new top frames")
    result = list(deepcopy(template))
    old_top = result[-1]
    result[-1] = replace(old_top, control=Control.suspended(old_top.control.frames))
    result.append(deepcopy(frame))
    return tuple(result)


def _rename_reference(reference: Optional[str], renaming: Dict[str, str]) -> Optional[str]:
    return renaming.get(reference, reference) if reference is not None else None


def copy_stack_frame_segment(
    template: Tuple[FrameTemplate, ...], start: int, end: int, names: Tuple[str, ...]
) -> Tuple[FrameTemplate, ...]:
    if start < 0 or end < start or end >= len(template) or len(names) != end - start + 1:
        raise DebuggerError("invalid copied segment")
    segment = deepcopy(template[start : end + 1])
    renaming = {frame.key: fresh_key(name) for frame, name in zip(segment, names)}
    result = []
    for frame in segment:
        record = deepcopy(frame.record)
        record.continuation = _rename_reference(record.continuation, renaming)
        record.home = _rename_reference(record.home, renaming)
        record.lexical_environment = {
            declaration: _rename_reference(activation, renaming)  # type: ignore[arg-type]
            for declaration, activation in record.lexical_environment.items()
        }
        result.append(replace(frame, key=renaming[frame.key], record=record))
    return tuple(result)


def _resolve_reference(reference: Optional[str], resolution: Dict[str, str]) -> Optional[str]:
    if reference is None:
        return None
    return resolution.get(reference, reference)


def materialize_stack_template(
    heap: Dict[str, Activation], old_stack: Tuple[str, ...], template: Tuple[FrameTemplate, ...], fresh
) -> Tuple[Dict[str, Activation], Tuple[str, ...], str]:
    if not template:
        raise DebuggerError("installed stack must be nonempty")
    keys = [frame.key for frame in template]
    if len(keys) != len(set(keys)):
        raise DebuggerError("template keys must be unique")

    resolution: Dict[str, str] = {}
    for key in keys:
        if key.startswith("retain:"):
            activation = key.split(":", 1)[1]
            if activation not in heap:
                raise DebuggerError(f"cannot retain missing activation {activation}")
            resolution[key] = activation
        elif key.startswith("fresh:"):
            resolution[key] = fresh()
        else:
            raise DebuggerError(f"unknown frame key {key}")
    if len(set(resolution.values())) != len(resolution):
        raise DebuggerError("resolved activation identities must be unique")

    controls = [frame.control for frame in template]
    if any(control.active for control in controls[:-1]) or not controls[-1].active:
        raise DebuggerError("exactly the top frame must be active")

    candidate = deepcopy(heap)
    new_stack = tuple(resolution[key] for key in keys)
    removed = set(old_stack) - set(new_stack)
    for activation in removed:
        if activation in candidate:
            candidate[activation].continuation = None
            candidate[activation].continuable = False

    for frame in template:
        activation = deepcopy(frame.record)
        activation.continuation = _resolve_reference(activation.continuation, resolution)
        activation.home = _resolve_reference(activation.home, resolution)
        activation.lexical_environment = {
            declaration: _resolve_reference(reference, resolution)  # type: ignore[dict-item]
            for declaration, reference in activation.lexical_environment.items()
        }
        candidate[resolution[frame.key]] = activation

    for index, activation_id in enumerate(new_stack):
        activation = candidate[activation_id]
        if not activation.continuable:
            raise DebuggerError("a live frame must be continuable")
        if activation.continuation is not None:
            lower = set(new_stack[:index])
            if activation.continuation not in lower:
                raise DebuggerError("continuation must name a lower live frame")
        if activation.home is not None and activation.home not in candidate:
            raise DebuggerError("home activation must exist")

    return candidate, new_stack, controls[-1].term  # type: ignore[return-value]


class DebuggerVM:
    def __init__(self, heap: Dict[str, Activation], actors: Dict[str, ActorState]):
        self.heap = deepcopy(heap)
        self.actors = deepcopy(actors)
        self._next_activation = 0
        self._next_token = 0

    def _fresh_activation(self) -> str:
        self._next_activation += 1
        return f"copied-{self._next_activation}"

    def _fresh_token(self) -> str:
        self._next_token += 1
        return f"pause-{self._next_token}"

    def pause_actor(self, caller: str, target: str, reason: str) -> str:
        state = self.actors[target]
        if caller == target or state.mode != "running" or not state.stack:
            raise DebuggerError("only another actor can pause a nonempty running actor")
        token = self._fresh_token()
        self.actors[target] = replace(
            state, mode="paused", pause_token=token, stop_reason=reason
        )
        return token

    def replace_paused_stack(self, target: str, token: str, template: Tuple[FrameTemplate, ...]) -> str:
        state = self.actors[target]
        if state.mode != "paused" or state.pause_token != token:
            raise DebuggerError("stale or invalid pause token")
        heap, stack, term = materialize_stack_template(
            self.heap, state.stack, template, self._fresh_activation
        )
        next_token = self._fresh_token()
        self.heap = heap
        self.actors[target] = replace(
            state, stack=stack, term=term, pause_token=next_token
        )
        return next_token

    def resume_paused_actor_at_full_speed(self, target: str, token: str) -> None:
        state = self.actors[target]
        if state.mode != "paused" or state.pause_token != token:
            raise DebuggerError("stale or invalid pause token")
        self.actors[target] = replace(
            state, mode="running", pause_token=None, stop_reason=None
        )

    def replace_and_resume_paused_stack(
        self, target: str, token: str, template: Tuple[FrameTemplate, ...]
    ) -> None:
        next_token = self.replace_paused_stack(target, token, template)
        self.resume_paused_actor_at_full_speed(target, next_token)

    def replace_current_actor_stack(
        self, caller: str, target: str, template: Tuple[FrameTemplate, ...]
    ) -> None:
        if caller != target:
            raise DebuggerError("a running stack may replace only itself")
        state = self.actors[target]
        if state.mode != "running":
            raise DebuggerError("current-stack replacement requires a running actor")
        heap, stack, term = materialize_stack_template(
            self.heap, state.stack, template, self._fresh_activation
        )
        self.heap = heap
        self.actors[target] = replace(state, stack=stack, term=term)
