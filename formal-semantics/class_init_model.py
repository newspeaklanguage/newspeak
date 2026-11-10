"""Non-normative executable oracle for Newspeak class initialization.

The LaTeX rules are normative.  This model pins down their identity, ordering,
slot-layout, lazy-slot, and nested-class-cache consequences.
"""

from dataclasses import dataclass, field
from itertools import count
from typing import Any, Callable, Dict, Iterable, Optional, Tuple


Initializer = Callable[["Runtime", "ObjectRecord", "ClassRecord", Tuple[Any, ...]], None]
StorageKey = Tuple[str, str]


@dataclass(frozen=True)
class Mixin:
    identity: str
    slots: Tuple[str, ...] = ()
    initializer: Optional[Initializer] = None


@dataclass
class ClassRecord:
    identity: str
    mixin: Mixin
    superclass: Optional["ClassRecord"]
    enclosing_object: Any
    metaclass: str
    factory_selector: str
    factory_arity: int


@dataclass
class ObjectRecord:
    identity: str
    cls: ClassRecord
    slots: Dict[StorageKey, Any]
    nested_classes: Dict[StorageKey, ClassRecord] = field(default_factory=dict)


class PullFuture:
    def __init__(self, thunk: Callable[[], Any], trace: list[str], name: str):
        self._thunk = thunk
        self._trace = trace
        self._name = name
        self._resolved = False
        self._value: Any = None

    def resolve(self) -> Any:
        if not self._resolved:
            self._trace.append(f"resolve:{self._name}")
            self._value = self._thunk()
            self._resolved = True
        return self._value


class Runtime:
    def __init__(self) -> None:
        self._ids = count(1)
        self.trace: list[str] = []

    def _fresh(self, prefix: str) -> str:
        return f"{prefix}{next(self._ids)}"

    def new_class(
        self,
        mixin: Mixin,
        superclass: Optional[ClassRecord],
        enclosing_object: Any,
        factory_selector: str = "new",
        factory_arity: int = 0,
    ) -> ClassRecord:
        return ClassRecord(
            identity=self._fresh("C"),
            mixin=mixin,
            superclass=superclass,
            enclosing_object=enclosing_object,
            metaclass=self._fresh("Meta"),
            factory_selector=factory_selector,
            factory_arity=factory_arity,
        )

    def apply_mixin(
        self,
        superclass: ClassRecord,
        superclass_message_selector: str,
        source: ClassRecord,
        mixin_message_selector: str,
    ) -> ClassRecord:
        if superclass_message_selector != superclass.factory_selector:
            raise ValueError("wrong superclass factory")
        if mixin_message_selector != source.factory_selector:
            raise ValueError("wrong mixin factory")
        return self.new_class(
            source.mixin,
            superclass,
            source.enclosing_object,
            mixin_message_selector,
            source.factory_arity,
        )

    def layout(self, cls: Optional[ClassRecord]) -> Tuple[StorageKey, ...]:
        if cls is None:
            return ()
        return self.layout(cls.superclass) + tuple((cls.identity, slot) for slot in cls.mixin.slots)

    def basic_new(self, cls: ClassRecord) -> ObjectRecord:
        return ObjectRecord(
            identity=self._fresh("o"),
            cls=cls,
            slots={slot: None for slot in self.layout(cls)},
        )

    def initialize(self, obj: ObjectRecord, cls: ClassRecord, args: Tuple[Any, ...] = ()) -> None:
        if len(args) != cls.factory_arity:
            raise ValueError("wrong factory arity")
        if cls.superclass is not None:
            self.initialize(obj, cls.superclass, ())
        self.trace.append(f"init:{cls.mixin.identity}")
        if cls.mixin.initializer is not None:
            cls.mixin.initializer(self, obj, cls, args)

    def new_instance(self, cls: ClassRecord, args: Tuple[Any, ...] = ()) -> ObjectRecord:
        obj = self.basic_new(cls)
        self.initialize(obj, cls, args)
        return obj

    def sequential_slots(
        self,
        obj: ObjectRecord,
        application: ClassRecord,
        initializers: Iterable[Tuple[str, Callable[[], Any]]],
    ) -> None:
        for slot, initializer in initializers:
            obj.slots[(application.identity, slot)] = initializer()

    def simultaneous_slots(
        self,
        obj: ObjectRecord,
        application: ClassRecord,
        initializers: Iterable[Tuple[str, Callable[[], Any]]],
    ) -> None:
        installed = []
        for slot, initializer in initializers:
            future = PullFuture(initializer, self.trace, slot)
            obj.slots[(application.identity, slot)] = future
            installed.append(future)
        for future in installed:
            future.resolve()

    def lazy_read(self, obj: ObjectRecord, application: ClassRecord, slot: str, initializer: Callable[[], Any]) -> Any:
        address = (application.identity, slot)
        value = obj.slots[address]
        if value is None:
            value = initializer()
            obj.slots[address] = value
        return value

    def nested_class(
        self,
        receiver: ObjectRecord,
        application: ClassRecord,
        declaration: str,
        constructor: Callable[[Any], ClassRecord],
    ) -> ClassRecord:
        key = (application.identity, declaration)
        cached = receiver.nested_classes.get(key)
        if cached is None:
            cached = constructor(receiver)
            receiver.nested_classes[key] = cached
        return cached
