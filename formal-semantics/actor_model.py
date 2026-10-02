"""Non-normative executable oracle for Newspeak actor routing.

The LaTeX rules are normative.  This small model pins down remote
representation, immediate promises, causal delivery, and dependent sends.
"""

from dataclasses import dataclass, field
from itertools import count
from typing import Any, Dict, List, Literal, Tuple


@dataclass(frozen=True)
class Near:
    actor: str
    identity: str


@dataclass(frozen=True)
class Far:
    actor: str
    identity: str


@dataclass(frozen=True)
class Value:
    payload: Any


@dataclass(frozen=True)
class PromiseRef:
    identity: str


@dataclass(frozen=True)
class Message:
    selector: str
    arguments: Tuple[Any, ...] = ()


@dataclass
class Waiter:
    actor: str
    message: Message
    result: PromiseRef
    history: frozenset[str]


@dataclass
class PromiseState:
    owner: str
    status: Literal["pending", "fulfilled", "broken"] = "pending"
    result_actor: str | None = None
    result: Any = None
    waiters: List[Waiter] = field(default_factory=list)


@dataclass(frozen=True)
class Packet:
    event: str
    source: str
    destination: str
    target: Near
    message: Message
    reply: PromiseRef
    history: frozenset[str]


class ActorWorld:
    def __init__(self, actors: Tuple[str, ...]) -> None:
        self._ids = count(1)
        self.histories: Dict[str, set[str]] = {a: set() for a in actors}
        self.delivered: Dict[str, List[str]] = {a: [] for a in actors}
        self.mailboxes: Dict[str, List[Packet]] = {a: [] for a in actors}
        self.network: List[Packet] = []
        self.destinations: Dict[str, str] = {}
        self.promises: Dict[PromiseRef, PromiseState] = {}

    def _fresh(self, prefix: str) -> str:
        return f"{prefix}{next(self._ids)}"

    def remote_representation(self, source: str, destination: str, obj: Any) -> Any:
        if source == destination:
            return obj
        if isinstance(obj, Value):
            return obj
        if isinstance(obj, PromiseRef):
            return obj
        if isinstance(obj, Far):
            if obj.actor == destination:
                return Near(destination, obj.identity)
            return obj
        if isinstance(obj, Near):
            if obj.actor != source:
                raise ValueError("near reference is not in the source actor")
            return Far(source, obj.identity)
        raise TypeError(f"not a transferable reference: {obj!r}")

    def _new_promise(self, owner: str) -> PromiseRef:
        promise = PromiseRef(self._fresh("p"))
        self.promises[promise] = PromiseState(owner)
        return promise

    def async_send(self, actor: str, receiver: Any, message: Message) -> PromiseRef:
        result = self._new_promise(actor)
        self._route(actor, receiver, message, result, frozenset(self.histories[actor]))
        return result

    def _route(
        self,
        actor: str,
        receiver: Any,
        message: Message,
        result: PromiseRef,
        history: frozenset[str],
    ) -> None:
        if isinstance(receiver, PromiseRef):
            state = self.promises[receiver]
            if state.status == "pending":
                state.waiters.append(Waiter(actor, message, result, history))
                return
            represented = self.remote_representation(
                state.result_actor or state.owner, actor, state.result
            )
            if state.status == "broken":
                self.settle(result, "broken", actor, represented)
                return
            self._route(actor, represented, message, result, history)
            return

        if isinstance(receiver, Near):
            if receiver.actor != actor:
                raise ValueError("foreign near reference")
            destination = actor
            target = receiver
        elif isinstance(receiver, Far):
            destination = receiver.actor
            target = Near(destination, receiver.identity)
        else:
            raise TypeError("eventual receiver must be near, far, or promised")

        transported = Message(
            message.selector,
            tuple(
                self.remote_representation(actor, destination, argument)
                for argument in message.arguments
            ),
        )
        event = self._fresh("e")
        packet = Packet(event, actor, destination, target, transported, result, history)
        self.destinations[event] = destination
        self.histories[actor].add(event)
        if actor == destination:
            self.mailboxes[destination].append(packet)
            self.delivered[destination].append(event)
        else:
            self.network.append(packet)

    def eligible(self, packet: Packet) -> bool:
        delivered = set(self.delivered[packet.destination])
        required = {
            event
            for event in packet.history
            if self.destinations[event] == packet.destination
        }
        return required <= delivered

    def deliver(self, packet: Packet) -> None:
        if packet not in self.network:
            raise ValueError("packet is not in flight")
        if not self.eligible(packet):
            raise ValueError("E-order predecessor has not arrived")
        self.network.remove(packet)
        self.mailboxes[packet.destination].append(packet)
        self.delivered[packet.destination].append(packet.event)

    def dequeue(self, actor: str) -> Packet:
        packet = self.mailboxes[actor].pop(0)
        self.histories[actor].update(packet.history)
        self.histories[actor].add(packet.event)
        return packet

    def settle(
        self,
        promise: PromiseRef,
        status: Literal["fulfilled", "broken"],
        source: str,
        result: Any,
    ) -> None:
        state = self.promises[promise]
        if state.status != "pending":
            raise ValueError("promise already settled")
        represented = self.remote_representation(source, state.owner, result)
        state.status = status
        state.result_actor = state.owner
        state.result = represented
        waiters = tuple(state.waiters)
        state.waiters.clear()
        for waiter in waiters:
            waiter_result = self.remote_representation(state.owner, waiter.actor, represented)
            if status == "broken":
                self.settle(waiter.result, "broken", waiter.actor, waiter_result)
            else:
                self._route(
                    waiter.actor,
                    waiter_result,
                    waiter.message,
                    waiter.result,
                    waiter.history,
                )
