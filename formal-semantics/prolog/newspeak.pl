% Newspeak relational semantics bridge.
%
% This file is proof-facing source.  Keep it within the subset documented in
% README.md.  In particular, absence is represented by none and never by
% negation as failure.

% --------------------------------------------------------------------------
% Finite semantic stores and record projections
% --------------------------------------------------------------------------

% A store is store([entry(Key, Value), ...]).  Well-formed stores have unique
% keys.  `dif/2` is the only constraint primitive admitted by the bridge.

% @latex equation:program-definition
% @lean Newspeak.FiniteStore
% @mode store_lookup(+,+,-)
store_lookup(store([]), _Key, none).

% @latex equation:program-definition
% @lean Newspeak.FiniteStore
% @mode store_lookup(+,+,-)
store_lookup(store([entry(Key, Value)|_Tail]), Key, some(Value)).

% @latex equation:program-definition
% @lean Newspeak.FiniteStore
% @mode store_lookup(+,+,-)
store_lookup(store([entry(Other, _Value)|Tail]), Key, Result) :-
    dif(Key, Other),
    store_lookup(store(Tail), Key, Result).

% @latex equation:program-definition
% @variant entry-keys-empty
% @lean Newspeak.FiniteStore.domain
% @mode store_entry_keys(+,-)
store_entry_keys([], []).

% @latex equation:program-definition
% @variant entry-keys-step
% @lean Newspeak.FiniteStore.domain
% @mode store_entry_keys(+,-)
store_entry_keys([entry(Key, _Value) | Remaining], [Key | Keys]) :-
    store_entry_keys(Remaining, Keys).

% Programs and heaps use extensible named fields so later slices can add the
% remaining components of equations (3.4) and (3.8) without changing terms
% already used by this slice.  Static well-formedness makes field names unique.

% @latex equation:program-definition
% @lean Newspeak.Program
% @mode program_field(+,+,-)
program_field(program(Fields), Name, Value) :-
    store_lookup(Fields, Name, some(Value)).

% @latex equation:heap-records
% @lean Newspeak.Heap
% @mode heap_field(+,+,-)
heap_field(heap(Fields), Name, Value) :-
    store_lookup(Fields, Name, some(Value)).

% @latex equation:program-definition
% @lean Newspeak.Program.top
% @mode top_class(+,-)
top_class(Program, Top) :-
    program_field(Program, top, Top).

% @latex equation:program-definition
% @lean Newspeak.Program.mixins
% @mode program_mixins(+,-)
program_mixins(Program, Mixins) :-
    program_field(Program, mixins, Mixins).

% @latex equation:heap-records
% @lean Newspeak.Heap.classes
% @mode heap_classes(+,-)
heap_classes(Heap, Classes) :-
    heap_field(Heap, classes, Classes).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.access
% @mode method_access(+,-)
method_access(
    method_def(_Identity, _Activation, _Selector, Access,
               _Parameters, _Locals, _Owner, _Body),
    Access).

% @latex equation:direct
% @lean Newspeak.Program.direct
% @mode direct(+,+,+,+,-)
direct(Program, Heap, Class, Selector, Result) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, ClassResult),
    direct_from_class(Program, Selector, ClassResult, Result).

% @latex equation:direct
% @lean Newspeak.Program.direct
% @mode direct_from_class(+,+,+,-)
direct_from_class(_Program, _Selector, none, none).

% @latex equation:direct
% @lean Newspeak.Program.direct
% @mode direct_from_class(+,+,+,-)
direct_from_class(Program, Selector,
                  some(class_def(Mixin, _Superclass, _EnclosingObject,
                                 _Metaclass, _Origin, _Factory)),
                  Result) :-
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, MixinResult),
    direct_from_mixin(Selector, MixinResult, Result).

% @latex equation:direct
% @lean Newspeak.Program.direct
% @mode direct_from_mixin(+,+,-)
direct_from_mixin(_Selector, none, none).

% @latex equation:direct
% @lean Newspeak.Program.direct
% @mode direct_from_mixin(+,+,-)
direct_from_mixin(Selector,
                  some(mixin_def(_Declaration, Methods, _OwnSlots,
                                 _NestedDeclarations,
                                 _InitializerDeclaration,
                                 _InitializerSelector,
                                 _InitializerParameters,
                                 _InitializerGroups,
                                 _InitializerBody)),
                  Result) :-
    store_lookup(Methods, Selector, Result).

% @latex equation:class-chain
% @lean Newspeak.Program.superclass?
% @mode superclass(+,+,+,-)
superclass(Program, _Heap, Class, none) :-
    top_class(Program, Class).

% @latex equation:class-chain
% @lean Newspeak.Program.superclass?
% @mode superclass(+,+,+,-)
superclass(Program, Heap, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, ClassResult),
    superclass_from_class(ClassResult, Result).

% @latex equation:class-chain
% @lean Newspeak.Program.superclass?
% @mode superclass_from_class(+,-)
superclass_from_class(none, none).

% @latex equation:class-chain
% @lean Newspeak.Program.superclass?
% @mode superclass_from_class(+,-)
superclass_from_class(
    some(class_def(_Mixin, Parent, _EnclosingObject,
                   _Metaclass, _Origin, _Factory)),
    some(Parent)).

% --------------------------------------------------------------------------
% Class chains and unrestricted lookup
% --------------------------------------------------------------------------

% @latex equation:class-chain
% @lean Newspeak.Program.ClassChain.top
% @mode class_chain(+,+,+,-)
class_chain(Program, _Heap, Top, [Top]) :-
    top_class(Program, Top).

% @latex equation:class-chain
% @lean Newspeak.Program.ClassChain.step
% @mode class_chain(+,+,+,-)
class_chain(Program, Heap, Class, [Class|Tail]) :-
    top_class(Program, Top),
    dif(Class, Top),
    superclass(Program, Heap, Class, some(Parent)),
    class_chain(Program, Heap, Parent, Tail).

% @latex rule:U-Top
% @lean Newspeak.Program.UnrestrictedLookupRules.top
% @mode unrestricted_lookup(+,+,+,+,-)
unrestricted_lookup(Program, _Heap, _Selector, Top, none) :-
    top_class(Program, Top).

% @latex rule:U-Here
% @lean Newspeak.Program.UnrestrictedLookupRules.here
% @mode unrestricted_lookup(+,+,+,+,-)
unrestricted_lookup(Program, Heap, Selector, Class,
                    some(lookup_result(Method, Class))) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)).

% @latex rule:U-Super
% @lean Newspeak.Program.UnrestrictedLookupRules.super
% @mode unrestricted_lookup(+,+,+,+,-)
unrestricted_lookup(Program, Heap, Selector, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, none),
    superclass(Program, Heap, Class, some(Parent)),
    unrestricted_lookup(Program, Heap, Selector, Parent, Result).

% The defining-class judgment is intentionally independent, as in the LaTeX.

% @latex rule:Defining-Top
% @lean Newspeak.PrologBridge.PrologDefiningClass.top
% @mode defining_class(+,+,+,+,-)
defining_class(Program, _Heap, _Selector, Top, none) :-
    top_class(Program, Top).

% @latex rule:Defining-Here
% @lean Newspeak.PrologBridge.PrologDefiningClass.here
% @mode defining_class(+,+,+,+,-)
defining_class(Program, Heap, Selector, Class, some(Class)) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(_Method)).

% @latex rule:Defining-Super
% @lean Newspeak.PrologBridge.PrologDefiningClass.super
% @mode defining_class(+,+,+,+,-)
defining_class(Program, Heap, Selector, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, none),
    superclass(Program, Heap, Class, some(Parent)),
    defining_class(Program, Heap, Selector, Parent, Result).

% --------------------------------------------------------------------------
% Public lookup
% --------------------------------------------------------------------------

% @latex rule:Pub-Top
% @lean Newspeak.Program.PublicLookupRules.top
% @mode public_lookup(+,+,+,+,-)
public_lookup(Program, _Heap, _Selector, Top, none) :-
    top_class(Program, Top).

% @latex rule:Pub-Hit
% @lean Newspeak.Program.PublicLookupRules.hit
% @mode public_lookup(+,+,+,+,-)
public_lookup(Program, Heap, Selector, Class,
              some(lookup_result(Method, Class))) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)),
    method_access(Method, public_access).

% @latex rule:Pub-Protected-Barrier
% @lean Newspeak.Program.PublicLookupRules.protectedBarrier
% @mode public_lookup(+,+,+,+,-)
public_lookup(Program, Heap, Selector, Class, none) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)),
    method_access(Method, protected_access).

% The disjunction in Pub-Super is represented by two Horn clauses.

% @latex rule:Pub-Super
% @variant absent
% @lean Newspeak.Program.PublicLookupRules.superAbsent
% @mode public_lookup(+,+,+,+,-)
public_lookup(Program, Heap, Selector, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, none),
    superclass(Program, Heap, Class, some(Parent)),
    public_lookup(Program, Heap, Selector, Parent, Result).

% @latex rule:Pub-Super
% @variant private
% @lean Newspeak.Program.PublicLookupRules.superPrivate
% @mode public_lookup(+,+,+,+,-)
public_lookup(Program, Heap, Selector, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)),
    method_access(Method, private_access),
    superclass(Program, Heap, Class, some(Parent)),
    public_lookup(Program, Heap, Selector, Parent, Result).

% --------------------------------------------------------------------------
% Protected lookup
% --------------------------------------------------------------------------

% @latex rule:Prot-Top
% @lean Newspeak.Program.ProtectedLookupRules.top
% @mode protected_lookup(+,+,+,+,-)
protected_lookup(Program, _Heap, _Selector, Top, none) :-
    top_class(Program, Top).

% The access-set premise of Prot-Hit is represented by two Horn clauses.

% @latex rule:Prot-Hit
% @variant public
% @lean Newspeak.Program.ProtectedLookupRules.hitPublic
% @mode protected_lookup(+,+,+,+,-)
protected_lookup(Program, Heap, Selector, Class,
                 some(lookup_result(Method, Class))) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)),
    method_access(Method, public_access).

% @latex rule:Prot-Hit
% @variant protected
% @lean Newspeak.Program.ProtectedLookupRules.hitProtected
% @mode protected_lookup(+,+,+,+,-)
protected_lookup(Program, Heap, Selector, Class,
                 some(lookup_result(Method, Class))) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)),
    method_access(Method, protected_access).

% @latex rule:Prot-Super
% @variant absent
% @lean Newspeak.Program.ProtectedLookupRules.superAbsent
% @mode protected_lookup(+,+,+,+,-)
protected_lookup(Program, Heap, Selector, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, none),
    superclass(Program, Heap, Class, some(Parent)),
    protected_lookup(Program, Heap, Selector, Parent, Result).

% @latex rule:Prot-Super
% @variant private
% @lean Newspeak.Program.ProtectedLookupRules.superPrivate
% @mode protected_lookup(+,+,+,+,-)
protected_lookup(Program, Heap, Selector, Class, Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    direct(Program, Heap, Class, Selector, some(Method)),
    method_access(Method, private_access),
    superclass(Program, Heap, Class, some(Parent)),
    protected_lookup(Program, Heap, Selector, Parent, Result).

% --------------------------------------------------------------------------
% Runtime projections used by dispatch
% --------------------------------------------------------------------------

% @latex equation:program-definition
% @lean Newspeak.Program.object
% @mode object_class(+,-)
object_class(Program, ObjectClass) :-
    program_field(Program, object, ObjectClass).

% @latex equation:heap-records
% @lean Newspeak.Heap.objects
% @mode heap_objects(+,-)
heap_objects(Heap, Objects) :-
    heap_field(Heap, objects, Objects).

% @latex equation:heap-records
% @lean Newspeak.Heap.mixinObjects
% @mode heap_mixin_objects(+,-)
heap_mixin_objects(Heap, Mixins) :-
    heap_field(Heap, mixin_objects, Mixins).

% @latex equation:heap-records
% @lean Newspeak.Heap.activations
% @mode heap_activations(+,-)
heap_activations(Heap, Activations) :-
    heap_field(Heap, activations, Activations).

% @latex equation:heap-records
% @lean Newspeak.Heap.closures
% @mode heap_closures(+,-)
heap_closures(Heap, Closures) :-
    heap_field(Heap, closures, Closures).

% @latex equation:heap-records
% @lean Newspeak.Heap.mirrors
% @mode heap_mirrors(+,-)
heap_mirrors(Heap, Mirrors) :-
    heap_field(Heap, mirrors, Mirrors).

% @latex equation:heap-records
% @lean Newspeak.Heap.actors
% @mode heap_actors(+,-)
heap_actors(Heap, Actors) :-
    heap_field(Heap, actors, Actors).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, ordinary_object(Id), Result) :-
    heap_objects(Heap, Objects),
    store_lookup(Objects, Id, ObjectResult),
    class_of_object(ObjectResult, Result).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, class_object(Id), Result) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Id, ClassResult),
    class_of_class(ClassResult, Result).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, mixin_object(Id), Result) :-
    heap_mixin_objects(Heap, Mixins),
    store_lookup(Mixins, Id, Result).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, activation_object(Id), Result) :-
    heap_activations(Heap, Activations),
    store_lookup(Activations, Id, ActivationResult),
    class_of_activation(ActivationResult, Result).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, closure_object(Id), Result) :-
    heap_closures(Heap, Closures),
    store_lookup(Closures, Id, ClosureResult),
    class_of_closure(ClosureResult, Result).

% @latex equation:mirror-record
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, mirror_object(Id), Result) :-
    heap_mirrors(Heap, Mirrors),
    store_lookup(Mirrors, Id, MirrorResult),
    class_of_mirror(MirrorResult, Result).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of(+,+,-)
class_of(Heap, actor_object(Id), Result) :-
    heap_actors(Heap, Actors),
    store_lookup(Actors, Id, ActorResult),
    class_of_actor(ActorResult, Result).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_object(+,-)
class_of_object(none, none).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_object(+,-)
class_of_object(
    some(object_def(Class, _Slots, _NestedClasses, _WeakContainer)),
    some(Class)).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_class(+,-)
class_of_class(none, none).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_class(+,-)
class_of_class(
    some(class_def(_Mixin, _Superclass, _EnclosingObject,
                   Metaclass, _Origin, _Factory)),
    some(Metaclass)).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_activation(+,-)
class_of_activation(none, none).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_activation(+,-)
class_of_activation(
    some(activation_def(ObjectClass, _Provenance, _Parameters, _Locals,
                        _Receiver, _CurrentClass, _Continuation, _HomeMethod,
                        _Continuable, _ActivationScopes,
                        _ObjectLiteralScopes)),
    some(ObjectClass)).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_closure(+,-)
class_of_closure(none, none).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_closure(+,-)
class_of_closure(
    some(closure_def(Class, _Declaration, _Parameters, _Locals, _Body,
                     _DefiningActivation, _Receiver, _CapturedClass,
                     _HomeMethod)),
    some(Class)).

% @latex equation:mirror-record
% @lean Newspeak.Heap.classOf
% @mode class_of_mirror(+,-)
class_of_mirror(none, none).

% @latex equation:mirror-record
% @lean Newspeak.Heap.classOf
% @mode class_of_mirror(+,-)
class_of_mirror(some(mirror_def(Class, _Payload)), some(Class)).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_actor(+,-)
class_of_actor(none, none).

% @latex equation:heap-records
% @lean Newspeak.Heap.classOf
% @mode class_of_actor(+,-)
class_of_actor(some(actor_def(Class)), some(Class)).

% @latex equation:heap-records
% @lean Newspeak.Heap.activations
% @mode activation_at(+,+,-)
activation_at(Heap, Id, Result) :-
    heap_activations(Heap, Activations),
    store_lookup(Activations, Id, Result).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.currentReceiver
% @mode activation_receiver(+,-)
activation_receiver(
    activation_def(_ObjectClass, _Provenance, _Parameters, _Locals,
                   Receiver, _CurrentClass, _Continuation, _HomeMethod,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Receiver).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.currentClass
% @mode activation_current_class(+,-)
activation_current_class(
    activation_def(_ObjectClass, _Provenance, _Parameters, _Locals,
                   _Receiver, CurrentClass, _Continuation, _HomeMethod,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    CurrentClass).

% @latex equation:method-definition
% @lean Newspeak.Message.selector
% @mode message_selector(+,-)
message_selector(message(Selector, _Arguments), Selector).

% --------------------------------------------------------------------------
% Ordinary and super dispatch
% --------------------------------------------------------------------------

% @latex rule:Send-Public
% @lean Newspeak.Program.OrdinaryDispatch.hit
% @mode ordinary_dispatch(+,+,+,+,-)
ordinary_dispatch(Program, Heap, Receiver, Message,
                  invoke(Method, Receiver, DefiningClass, Message)) :-
    class_of(Heap, Receiver, some(ReceiverClass)),
    message_selector(Message, Selector),
    public_lookup(Program, Heap, Selector, ReceiverClass,
                  some(lookup_result(Method, DefiningClass))).

% @latex rule:Send-Missing
% @lean Newspeak.Program.OrdinaryDispatch.missing
% @mode ordinary_dispatch(+,+,+,+,-)
ordinary_dispatch(Program, Heap, Receiver, Message,
                  missing(Receiver, ReceiverClass, Message)) :-
    class_of(Heap, Receiver, some(ReceiverClass)),
    message_selector(Message, Selector),
    public_lookup(Program, Heap, Selector, ReceiverClass, none).

% @latex rule:Super-Hit
% @lean Newspeak.Program.SuperDispatch.hit
% @mode super_dispatch(+,+,+,+,-)
super_dispatch(Program, Heap, ActivationId, Message,
               invoke(Method, Receiver, DefiningClass, Message)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    activation_current_class(Activation, some(CurrentClass)),
    object_class(Program, ObjectClass),
    top_class(Program, Top),
    dif(CurrentClass, ObjectClass),
    dif(CurrentClass, Top),
    superclass(Program, Heap, CurrentClass, some(LookupStart)),
    message_selector(Message, Selector),
    protected_lookup(Program, Heap, Selector, LookupStart,
                     some(lookup_result(Method, DefiningClass))),
    activation_receiver(Activation, Receiver).

% @latex rule:Super-Missing
% @lean Newspeak.Program.SuperDispatch.missing
% @mode super_dispatch(+,+,+,+,-)
super_dispatch(Program, Heap, ActivationId, Message,
               missing(Receiver, LookupStart, Message)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    activation_current_class(Activation, some(CurrentClass)),
    object_class(Program, ObjectClass),
    top_class(Program, Top),
    dif(CurrentClass, ObjectClass),
    dif(CurrentClass, Top),
    superclass(Program, Heap, CurrentClass, some(LookupStart)),
    message_selector(Message, Selector),
    protected_lookup(Program, Heap, Selector, LookupStart, none),
    activation_receiver(Activation, Receiver).

% @latex rule:Super-Object-Error
% @lean Newspeak.Program.SuperDispatch.objectError
% @mode super_dispatch(+,+,+,+,-)
super_dispatch(Program, Heap, ActivationId, _Message,
               invalid_super(ObjectClass)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    object_class(Program, ObjectClass),
    activation_current_class(Activation, some(ObjectClass)).

% @latex rule:Super-Top-Error
% @lean Newspeak.Program.SuperDispatch.topError
% @mode super_dispatch(+,+,+,+,-)
super_dispatch(Program, Heap, ActivationId, _Message,
               invalid_super(Top)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    top_class(Program, Top),
    activation_current_class(Activation, some(Top)).

% --------------------------------------------------------------------------
% Lexical classes, applications, and enclosing receivers
% --------------------------------------------------------------------------

% @latex equation:class-membership-depth
% @lean Newspeak.PrologBridge.PrologListMember.head
% @mode list_member(+,+)
list_member(Value, [Value|_Tail]).

% @latex equation:class-membership-depth
% @lean Newspeak.PrologBridge.PrologListMember.tail
% @mode list_member(+,+)
list_member(Value, [_Other|Tail]) :-
    list_member(Value, Tail).

% @latex equation:class-membership-depth
% @lean Newspeak.Program.ClassMember
% @mode class_member(+,+,+,+)
class_member(Program, Heap, Candidate, ReceiverClass) :-
    class_chain(Program, Heap, ReceiverClass, Chain),
    list_member(Candidate, Chain).

% @latex equation:program-definition
% @lean Newspeak.Program.lexParent
% @mode program_lex_parents(+,-)
program_lex_parents(Program, Parents) :-
    program_field(Program, lex_parent, Parents).

% @latex equation:scope-chain
% @variant store
% @lean Newspeak.Program.scopeChain
% @mode program_scope_chains(+,-)
program_scope_chains(Program, ScopeChains) :-
    program_field(Program, scope_chains, ScopeChains).

% @latex equation:scope-chain
% @lean Newspeak.Program.scopeChain
% @mode scope_chain(+,+,-)
scope_chain(Program, Site, Scopes) :-
    program_scope_chains(Program, ScopeChains),
    store_lookup(ScopeChains, Site, some(Scopes)).

% @latex equation:declares
% @variant store
% @lean Newspeak.Program.declares
% @mode program_declarations(+,-)
program_declarations(Program, Declarations) :-
    program_field(Program, declarations, Declarations).

% @latex equation:declares
% @lean Newspeak.Program.declares
% @mode declares(+,+,+,-)
declares(Program, Declaration, Selector, Result) :-
    program_declarations(Program, Declarations),
    store_lookup(
        Declarations, declaration_selector(Declaration, Selector),
        some(Result)).

% @latex equation:lexical-binding
% @variant empty
% @lean Newspeak.Program.bindIn
% @mode bind_in(+,+,+,-)
bind_in(_Program, _Selector, [], none).

% @latex equation:lexical-binding
% @variant hit
% @lean Newspeak.Program.bindIn
% @mode bind_in(+,+,+,-)
bind_in(Program, Selector, [Declaration|_Rest], some(Declaration)) :-
    declares(Program, Declaration, Selector, true).

% @latex equation:lexical-binding
% @variant skip
% @lean Newspeak.Program.bindIn
% @mode bind_in(+,+,+,-)
bind_in(Program, Selector, [Declaration|Rest], Result) :-
    declares(Program, Declaration, Selector, false),
    bind_in(Program, Selector, Rest, Result).

% @latex equation:lexical-binding
% @lean Newspeak.Program.bind
% @mode lexical_binding(+,+,+,-)
lexical_binding(Program, Site, Selector, Result) :-
    scope_chain(Program, Site, Scopes),
    bind_in(Program, Selector, Scopes, Result).

% @latex equation:lex-ancestor
% @lean Newspeak.Program.LexicalAncestor.zero
% @mode lexical_ancestor(+,+,+,-)
lexical_ancestor(_Program, Start, zero, Start).

% @latex equation:lex-ancestor
% @lean Newspeak.Program.LexicalAncestor.step
% @mode lexical_ancestor(+,+,+,-)
lexical_ancestor(Program, Start, succ(Depth), Target) :-
    program_lex_parents(Program, Parents),
    store_lookup(Parents, Start, some(Parent)),
    lexical_ancestor(Program, Parent, Depth, Target).

% @latex equation:lex-depth
% @lean Newspeak.Program.LexicalClassChain.root
% @mode lexical_class_chain(+,+,-)
lexical_class_chain(Program, Declaration, [Declaration]) :-
    program_lex_parents(Program, Parents),
    store_lookup(Parents, Declaration, none).

% @latex equation:lex-depth
% @lean Newspeak.Program.LexicalClassChain.step
% @mode lexical_class_chain(+,+,-)
lexical_class_chain(Program, Declaration, [Declaration|Tail]) :-
    program_lex_parents(Program, Parents),
    store_lookup(Parents, Declaration, some(Parent)),
    lexical_class_chain(Program, Parent, Tail).

% @latex equation:lex-depth
% @lean Newspeak.Program.lexicalDepthOnChain
% @mode lexical_depth_on_chain(+,+,-)
lexical_depth_on_chain(_Target, [], none).

% @latex equation:lex-depth
% @lean Newspeak.Program.lexicalDepthOnChain
% @mode lexical_depth_on_chain(+,+,-)
lexical_depth_on_chain(Target, [Target|_Tail], some(zero)).

% @latex equation:lex-depth
% @variant found-deeper
% @lean Newspeak.Program.lexicalDepthOnChain
% @mode lexical_depth_on_chain(+,+,-)
lexical_depth_on_chain(Target, [Other|Tail], some(succ(Depth))) :-
    dif(Other, Target),
    lexical_depth_on_chain(Target, Tail, some(Depth)).

% @latex equation:lex-depth
% @variant absent
% @lean Newspeak.Program.lexicalDepthOnChain
% @mode lexical_depth_on_chain(+,+,-)
lexical_depth_on_chain(Target, [Other|Tail], none) :-
    dif(Other, Target),
    lexical_depth_on_chain(Target, Tail, none).

% @latex equation:lex-depth
% @lean Newspeak.Program.LexicalDepth
% @mode lexical_depth(+,+,+,-)
lexical_depth(Program, Target, Start, Result) :-
    lexical_class_chain(Program, Start, Chain),
    lexical_depth_on_chain(Target, Chain, Result).

% @latex equation:class-scan
% @variant empty
% @lean Newspeak.Program.scanOnClassChain
% @mode scan_on_class_chain(+,+,+,-)
scan_on_class_chain(_Program, _Selector, [], none).

% @latex equation:class-scan
% @variant hit
% @lean Newspeak.Program.scanOnClassChain
% @mode scan_on_class_chain(+,+,+,-)
scan_on_class_chain(
    Program, Selector, [Declaration|_Rest], some(Declaration)) :-
    declares(Program, class_decl(Declaration), Selector, true).

% @latex equation:class-scan
% @variant skip
% @lean Newspeak.Program.scanOnClassChain
% @mode scan_on_class_chain(+,+,+,-)
scan_on_class_chain(Program, Selector, [Declaration|Rest], Result) :-
    declares(Program, class_decl(Declaration), Selector, false),
    scan_on_class_chain(Program, Selector, Rest, Result).

% @latex equation:class-scan
% @lean Newspeak.Program.ClassScan
% @mode class_scan(+,+,+,-)
class_scan(Program, Start, Selector, Result) :-
    lexical_class_chain(Program, Start, Chain),
    scan_on_class_chain(Program, Selector, Chain, Result).

% @latex equation:implicit-receiver
% @variant found
% @lean Newspeak.Program.ImplicitReceiver.found
% @mode implicit_receiver(+,+,+,+,+,-,-)
implicit_receiver(
    Program, Heap, Receiver, CurrentClass, Immediate,
    selected_receiver(Selected, some(Target)), Selector) :-
    class_scan(Program, Immediate, Selector, some(Target)),
    lexical_depth(Program, Target, Immediate, some(Depth)),
    enclosing_receiver(
        Program, Heap, Receiver, CurrentClass, Depth, Selected).

% @latex equation:implicit-receiver
% @variant absent
% @lean Newspeak.Program.ImplicitReceiver.absent
% @mode implicit_receiver(+,+,+,+,+,-,-)
implicit_receiver(
    Program, _Heap, Receiver, _CurrentClass, Immediate,
    selected_receiver(Receiver, none), Selector) :-
    class_scan(Program, Immediate, Selector, none).

% @latex equation:application-indices
% @variant empty
% @lean Newspeak.Program.applicationIndicesFrom
% @mode application_indices_from(+,+,+,+,+,-)
application_indices_from(
    _Program, _Heap, _Target, _Position, [], []).

% @latex equation:application-indices
% @variant top
% @lean Newspeak.Program.applicationIndicesFrom
% @mode application_indices_from(+,+,+,+,+,-)
application_indices_from(
    Program, Heap, Target, Position, [Class|Rest], Indices) :-
    top_class(Program, Class),
    application_indices_from(
        Program, Heap, Target, succ(Position), Rest, Indices).

% @latex equation:application-indices
% @variant match
% @lean Newspeak.Program.applicationIndicesFrom
% @mode application_indices_from(+,+,+,+,+,-)
application_indices_from(
    Program, Heap, Target, Position, [Class|Rest], [Position|Indices]) :-
    top_class(Program, Top),
    dif(Class, Top),
    named_class_declaration(Program, Heap, Class, some(Target)),
    application_indices_from(
        Program, Heap, Target, succ(Position), Rest, Indices).

% @latex equation:application-indices
% @variant different-declaration
% @lean Newspeak.Program.applicationIndicesFrom
% @mode application_indices_from(+,+,+,+,+,-)
application_indices_from(
    Program, Heap, Target, Position, [Class|Rest], Indices) :-
    top_class(Program, Top),
    dif(Class, Top),
    named_class_declaration(Program, Heap, Class, some(Other)),
    dif(Other, Target),
    application_indices_from(
        Program, Heap, Target, succ(Position), Rest, Indices).

% @latex equation:application-indices
% @variant no-declaration
% @lean Newspeak.Program.applicationIndicesFrom
% @mode application_indices_from(+,+,+,+,+,-)
application_indices_from(
    Program, Heap, Target, Position, [Class|Rest], Indices) :-
    top_class(Program, Top),
    dif(Class, Top),
    named_class_declaration(Program, Heap, Class, none),
    application_indices_from(
        Program, Heap, Target, succ(Position), Rest, Indices).

% @latex equation:application-indices
% @lean Newspeak.Program.ApplicationIndices
% @mode application_indices(+,+,+,+,-)
application_indices(Program, Heap, ReceiverClass, Target, Indices) :-
    class_chain(Program, Heap, ReceiverClass, Chain),
    application_indices_from(
        Program, Heap, Target, zero, Chain, Indices).

% @latex equation:program-definition
% @lean Newspeak.Program.declMixin
% @mode program_decl_mixins(+,-)
program_decl_mixins(Program, DeclMixins) :-
    program_field(Program, decl_mixins, DeclMixins).

% @latex equation:mixin-record
% @lean Newspeak.MixinDef.declaration
% @mode mixin_declaration(+,-)
mixin_declaration(
    mixin_def(Declaration, _Methods, _OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, _InitializerSelector,
              _InitializerParameters, _InitializerGroups, _InitializerBody),
    Declaration).

% @latex equation:nearest-application
% @lean Newspeak.Program.classBodyDeclaration?
% @mode class_body_declaration(+,+,+,-)
class_body_declaration(Program, Heap, Class, Result) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, ClassResult),
    class_body_from_class(Program, ClassResult, Result).

% @latex equation:nearest-application
% @lean Newspeak.Program.classBodyDeclaration?
% @mode class_body_from_class(+,+,-)
class_body_from_class(_Program, none, none).

% @latex equation:nearest-application
% @lean Newspeak.Program.classBodyDeclaration?
% @mode class_body_from_class(+,+,-)
class_body_from_class(
    Program,
    some(class_def(Mixin, _Superclass, _EnclosingObject,
                   _Metaclass, _Origin, _Factory)),
    Result) :-
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, MixinResult),
    class_body_from_mixin(MixinResult, Result).

% @latex equation:nearest-application
% @lean Newspeak.Program.classBodyDeclaration?
% @mode class_body_from_mixin(+,-)
class_body_from_mixin(none, none).

% @latex equation:nearest-application
% @lean Newspeak.Program.classBodyDeclaration?
% @mode class_body_from_mixin(+,-)
class_body_from_mixin(some(Mixin), some(Declaration)) :-
    mixin_declaration(Mixin, Declaration).

% @latex equation:nearest-application
% @lean Newspeak.Program.namedClassDeclaration?
% @mode named_class_declaration(+,+,+,-)
named_class_declaration(Program, Heap, Class, Result) :-
    class_body_declaration(Program, Heap, Class, BodyResult),
    named_declaration_from_body(BodyResult, Result).

% @latex equation:nearest-application
% @lean Newspeak.Program.namedClassDeclaration?
% @mode named_declaration_from_body(+,-)
named_declaration_from_body(none, none).

% @latex equation:nearest-application
% @lean Newspeak.Program.namedClassDeclaration?
% @mode named_declaration_from_body(+,-)
named_declaration_from_body(some(named_class(Declaration)), some(Declaration)).

% @latex equation:nearest-application
% @lean Newspeak.Program.namedClassDeclaration?
% @mode named_declaration_from_body(+,-)
named_declaration_from_body(some(object_literal(_Declaration)), none).

% @latex equation:nearest-application
% @lean Newspeak.Program.nearestApplicationOnChain
% @mode nearest_application_on_chain(+,+,+,+,-)
nearest_application_on_chain(_Program, _Heap, _Target, [], none).

% @latex equation:nearest-application
% @lean Newspeak.Program.nearestApplicationOnChain
% @mode nearest_application_on_chain(+,+,+,+,-)
nearest_application_on_chain(Program, _Heap, _Target, [Top|_Tail], none) :-
    top_class(Program, Top).

% @latex equation:nearest-application
% @lean Newspeak.Program.nearestApplicationOnChain
% @mode nearest_application_on_chain(+,+,+,+,-)
nearest_application_on_chain(Program, Heap, Target, [Class|_Tail], some(Class)) :-
    top_class(Program, Top),
    dif(Class, Top),
    named_class_declaration(Program, Heap, Class, some(Target)).

% @latex equation:nearest-application
% @variant absent
% @lean Newspeak.Program.nearestApplicationOnChain
% @mode nearest_application_on_chain(+,+,+,+,-)
nearest_application_on_chain(Program, Heap, Target, [Class|Tail], Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    named_class_declaration(Program, Heap, Class, none),
    nearest_application_on_chain(Program, Heap, Target, Tail, Result).

% @latex equation:nearest-application
% @variant other-declaration
% @lean Newspeak.Program.nearestApplicationOnChain
% @mode nearest_application_on_chain(+,+,+,+,-)
nearest_application_on_chain(Program, Heap, Target, [Class|Tail], Result) :-
    top_class(Program, Top),
    dif(Class, Top),
    named_class_declaration(Program, Heap, Class, some(Other)),
    dif(Other, Target),
    nearest_application_on_chain(Program, Heap, Target, Tail, Result).

% @latex equation:nearest-application
% @lean Newspeak.Program.NearestApplication
% @mode nearest_application(+,+,+,+,-)
nearest_application(Program, Heap, ReceiverClass, Target, Result) :-
    class_chain(Program, Heap, ReceiverClass, Chain),
    nearest_application_on_chain(Program, Heap, Target, Chain, Result).

% @latex equation:target-application
% @lean Newspeak.Program.TargetApplication
% @mode target_application(+,+,+,+,-)
target_application(Program, Heap, Receiver, Target, Result) :-
    class_of(Heap, Receiver, some(ReceiverClass)),
    nearest_application(Program, Heap, ReceiverClass, Target, Result).

% @latex equation:heap-records
% @lean Newspeak.ClassDef.enclosingObject
% @mode class_enclosing_object(+,+,-)
class_enclosing_object(Heap, Class, EnclosingObject) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDef)),
    class_definition_enclosing_object(ClassDef, EnclosingObject).

% @latex equation:heap-records
% @lean Newspeak.ClassDef.enclosingObject
% @mode class_definition_enclosing_object(+,-)
class_definition_enclosing_object(
    class_def(_Mixin, _Superclass, EnclosingObject,
              _Metaclass, _Origin, _Factory),
    EnclosingObject).

% @latex rule:Enc-Zero
% @lean Newspeak.Program.EnclosingReceiver.zero
% @mode enclosing_receiver(+,+,+,+,+,-)
enclosing_receiver(Program, Heap, Receiver, CurrentClass, zero, Receiver) :-
    class_of(Heap, Receiver, some(ReceiverClass)),
    class_member(Program, Heap, CurrentClass, ReceiverClass).

% @latex rule:Enc-One
% @lean Newspeak.Program.EnclosingReceiver.one
% @mode enclosing_receiver(+,+,+,+,+,-)
enclosing_receiver(Program, Heap, Receiver, CurrentClass, succ(zero), Enclosing) :-
    class_of(Heap, Receiver, some(ReceiverClass)),
    class_member(Program, Heap, CurrentClass, ReceiverClass),
    class_enclosing_object(Heap, CurrentClass, Enclosing).

% @latex rule:Enc-Step
% @lean Newspeak.Program.EnclosingReceiver.step
% @mode enclosing_receiver(+,+,+,+,+,-)
enclosing_receiver(Program, Heap, Receiver, CurrentClass,
                   succ(succ(Depth)), Enclosing) :-
    enclosing_receiver(Program, Heap, Receiver, CurrentClass,
                       succ(Depth), Previous),
    named_class_declaration(Program, Heap, CurrentClass, some(CurrentDecl)),
    lexical_ancestor(Program, CurrentDecl, succ(Depth), AncestorDecl),
    class_of(Heap, Previous, some(PreviousClass)),
    nearest_application(Program, Heap, PreviousClass, AncestorDecl,
                        some(Application)),
    class_enclosing_object(Heap, Application, Enclosing).

% --------------------------------------------------------------------------
% Outer, self, and implicit dispatch
% --------------------------------------------------------------------------

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method(+,+,+,-)
private_method(Program, Target, Selector, Result) :-
    program_decl_mixins(Program, DeclMixins),
    store_lookup(DeclMixins, named_class(Target), MixinResult),
    private_method_from_mixin_id(Program, Selector, MixinResult, Result).

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_mixin_id(+,+,+,-)
private_method_from_mixin_id(_Program, _Selector, none, none).

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_mixin_id(+,+,+,-)
private_method_from_mixin_id(Program, Selector, some(Mixin), Result) :-
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, MixinResult),
    private_method_from_mixin(Selector, MixinResult, Result).

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_mixin(+,+,-)
private_method_from_mixin(_Selector, none, none).

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_mixin(+,+,-)
private_method_from_mixin(Selector,
                          some(mixin_def(_Declaration, Methods, _OwnSlots,
                                         _NestedDeclarations,
                                         _InitializerDeclaration,
                                         _InitializerSelector,
                                         _InitializerParameters,
                                         _InitializerGroups,
                                         _InitializerBody)),
                          Result) :-
    store_lookup(Methods, Selector, MethodResult),
    private_method_from_method(MethodResult, Result).

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_method(+,-)
private_method_from_method(none, none).

% @latex equation:private-method
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_method(+,-)
private_method_from_method(some(Method), some(Method)) :-
    method_access(Method, private_access).

% @latex equation:private-method
% @variant public
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_method(+,-)
private_method_from_method(some(Method), none) :-
    method_access(Method, public_access).

% @latex equation:private-method
% @variant protected
% @lean Newspeak.Program.privateMethod
% @mode private_method_from_method(+,-)
private_method_from_method(some(Method), none) :-
    method_access(Method, protected_access).

% @latex rule:Outer-Private
% @lean Newspeak.Program.OuterDispatch.privateHit
% @mode outer_dispatch(+,+,+,+,+,+,-)
outer_dispatch(Program, Heap, ActivationId, Target, Immediate, Message,
               invoke(Method, Receiver, TargetApplication, Message)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    activation_current_class(Activation, some(CurrentClass)),
    lexical_depth(Program, Target, Immediate, some(Depth)),
    activation_receiver(Activation, CurrentReceiver),
    enclosing_receiver(Program, Heap, CurrentReceiver, CurrentClass,
                       Depth, Receiver),
    target_application(Program, Heap, Receiver, Target,
                       some(TargetApplication)),
    message_selector(Message, Selector),
    private_method(Program, Target, Selector, some(Method)).

% @latex rule:Outer-Protected
% @lean Newspeak.Program.OuterDispatch.protectedHit
% @mode outer_dispatch(+,+,+,+,+,+,-)
outer_dispatch(Program, Heap, ActivationId, Target, Immediate, Message,
               invoke(Method, Receiver, DefiningClass, Message)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    activation_current_class(Activation, some(CurrentClass)),
    lexical_depth(Program, Target, Immediate, some(Depth)),
    activation_receiver(Activation, CurrentReceiver),
    enclosing_receiver(Program, Heap, CurrentReceiver, CurrentClass,
                       Depth, Receiver),
    message_selector(Message, Selector),
    private_method(Program, Target, Selector, none),
    class_of(Heap, Receiver, some(ReceiverClass)),
    protected_lookup(Program, Heap, Selector, ReceiverClass,
                     some(lookup_result(Method, DefiningClass))).

% @latex rule:Outer-Missing
% @lean Newspeak.Program.OuterDispatch.missing
% @mode outer_dispatch(+,+,+,+,+,+,-)
outer_dispatch(Program, Heap, ActivationId, Target, Immediate, Message,
               missing(Receiver, ReceiverClass, Message)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    activation_current_class(Activation, some(CurrentClass)),
    lexical_depth(Program, Target, Immediate, some(Depth)),
    activation_receiver(Activation, CurrentReceiver),
    enclosing_receiver(Program, Heap, CurrentReceiver, CurrentClass,
                       Depth, Receiver),
    message_selector(Message, Selector),
    private_method(Program, Target, Selector, none),
    class_of(Heap, Receiver, some(ReceiverClass)),
    protected_lookup(Program, Heap, Selector, ReceiverClass, none).

% @latex equation:self-send-derived
% @lean Newspeak.Program.SelfDispatch
% @mode self_dispatch(+,+,+,+,+,-)
self_dispatch(Program, Heap, ActivationId, Immediate, Message, Result) :-
    outer_dispatch(Program, Heap, ActivationId, Immediate, Immediate,
                   Message, Result).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.activationScopes
% @mode activation_scope(+,+,-)
activation_scope(
    activation_def(_ObjectClass, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _HomeMethod,
                   _Continuable, ActivationScopes, _ObjectLiteralScopes),
    Declaration,
    Result) :-
    store_lookup(ActivationScopes, Declaration, Result).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.objectLiteralScopes
% @mode object_literal_scope(+,+,-)
object_literal_scope(
    activation_def(_ObjectClass, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _HomeMethod,
                   _Continuable, _ActivationScopes, ObjectLiteralScopes),
    Declaration,
    Result) :-
    store_lookup(ObjectLiteralScopes, Declaration, Result).

% @latex rule:Implicit-Class
% @also equation:implicit-judgment
% @lean Newspeak.Program.ImplicitDispatch.classScope
% @mode implicit_dispatch(+,+,+,+,+,+,-)
implicit_dispatch(Program, Heap, ActivationId, some(Immediate),
                  some(class_decl(Target)), Message, Result) :-
    outer_dispatch(Program, Heap, ActivationId, Target, Immediate,
                   Message, Result).

% @latex rule:Implicit-Literal
% @also equation:implicit-judgment
% @lean Newspeak.Program.ImplicitDispatch.objectLiteralScope
% @mode implicit_dispatch(+,+,+,+,+,+,-)
implicit_dispatch(Program, Heap, ActivationId, _Immediate,
                  some(object_literal_decl(Declaration)), Message,
                  invoke(Method, Receiver, DefiningClass, Message)) :-
    activation_at(Heap, ActivationId, some(Activation)),
    object_literal_scope(Activation, Declaration, some(Receiver)),
    class_of(Heap, Receiver, some(ReceiverClass)),
    message_selector(Message, Selector),
    unrestricted_lookup(Program, Heap, Selector, ReceiverClass,
                        some(lookup_result(Method, DefiningClass))),
    class_body_declaration(Program, Heap, DefiningClass,
                           some(object_literal(Declaration))).

% @latex rule:Implicit-Activation
% @also equation:implicit-judgment
% @lean Newspeak.Program.ImplicitDispatch.activationScope
% @mode implicit_dispatch(+,+,+,+,+,+,-)
implicit_dispatch(Program, Heap, ActivationId, _Immediate,
                  some(activation_decl(Declaration)), Message, Result) :-
    activation_at(Heap, ActivationId, some(Activation)),
    activation_scope(Activation, Declaration, some(TargetActivation)),
    ordinary_dispatch(Program, Heap, activation_object(TargetActivation),
                      Message, Result).

% @latex rule:Implicit-Self
% @also equation:implicit-judgment
% @lean Newspeak.Program.ImplicitDispatch.self
% @mode implicit_dispatch(+,+,+,+,+,+,-)
implicit_dispatch(Program, Heap, ActivationId, some(Immediate), none,
                  Message, Result) :-
    self_dispatch(Program, Heap, ActivationId, Immediate, Message, Result).

% --------------------------------------------------------------------------
% DNU selection and message-mirror allocation
% --------------------------------------------------------------------------

% `store_install/4` is the list-store presentation of FiniteStore.install:
% an absent key is prepended; replacement preserves the existing key order.

% @latex rule:DNU
% @variant store-install
% @lean Newspeak.FiniteStore.install
% @mode store_install(+,+,+,-)
store_install(Store, Key, Value, Result) :-
    store_lookup(Store, Key, Existing),
    store_install_known(Store, Key, Value, Existing, Result).

% @latex rule:DNU
% @variant store-install-absent
% @lean Newspeak.FiniteStore.install
% @mode store_install_known(+,+,+,+,-)
store_install_known(store(Entries), Key, Value, none,
                    store([entry(Key, Value)|Entries])).

% @latex rule:DNU
% @variant store-install-here
% @lean Newspeak.FiniteStore.install
% @mode store_install_known(+,+,+,+,-)
store_install_known(store([entry(Key, _Old)|Tail]), Key, Value, some(_Old),
                    store([entry(Key, Value)|Tail])).

% @latex rule:DNU
% @variant store-install-later
% @lean Newspeak.FiniteStore.install
% @mode store_install_known(+,+,+,+,-)
store_install_known(store([entry(Other, OtherValue)|Tail]), Key, Value,
                    some(Existing),
                    store([entry(Other, OtherValue)|NewTail])) :-
    dif(Key, Other),
    store_install_known(store(Tail), Key, Value, some(Existing),
                        store(NewTail)).

% @latex rule:DNU
% @variant message-mirror-class
% @lean Newspeak.Program.messageMirrorClass
% @mode message_mirror_class(+,-)
message_mirror_class(Program, Class) :-
    program_field(Program, message_mirror_class, Class).

% @latex rule:DNU
% @variant message-mirror-definition
% @lean Newspeak.Program.messageMirrorDefinition
% @mode message_mirror_definition(+,+,-)
message_mirror_definition(Program, Message,
                          mirror_def(Class, message_payload(Message))) :-
    message_mirror_class(Program, Class).

% @latex rule:DNU
% @variant heap-install-mirror
% @lean Newspeak.Heap.installMirror
% @mode heap_install_mirror(+,+,+,-)
heap_install_mirror(heap(Fields), Id, Mirror, heap(NewFields)) :-
    store_lookup(Fields, mirrors, some(Mirrors)),
    store_install(Mirrors, Id, Mirror, NewMirrors),
    store_install(Fields, mirrors, NewMirrors, NewFields).

% @latex rule:DNU
% @variant allocate-message-mirror
% @lean Newspeak.Program.allocateMessageMirror
% @mode allocate_message_mirror(+,+,+,-,-)
allocate_message_mirror(
    Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Message,
    allocation_state(NewHeap, succ(NextMirror), NextActivation, NextClosure,
                     NextObject, NextClass),
    mirror_object(mirror_id(NextMirror))) :-
    message_mirror_definition(Program, Message, Mirror),
    heap_install_mirror(Heap, mirror_id(NextMirror), Mirror, NewHeap).

% @latex rule:DNU
% @variant selection
% @lean Newspeak.Program.DnuSelection.found
% @mode dnu_selection(+,+,+,-)
dnu_selection(Program, Heap, LookupStart,
              lookup_result(Method, DefiningClass)) :-
    unrestricted_lookup(
        Program, Heap, selector('doesNotUnderstand:'), LookupStart,
        some(lookup_result(Method, DefiningClass))).

% @latex rule:DNU
% @variant finish
% @lean Newspeak.Program.finishDnu
% @mode finish_dnu(+,+,+,+,+,-,-)
finish_dnu(Program, State, Receiver, Original,
           lookup_result(Method, DefiningClass), NewState,
           invoke(Method, Receiver, DefiningClass,
                  message(selector('doesNotUnderstand:'), [Mirror]))) :-
    allocate_message_mirror(Program, State, Original, NewState, Mirror).

% @latex rule:DNU
% @variant fallback
% @lean Newspeak.Program.DnuFallback.apply
% @mode dnu_fallback(+,+,+,+,+,-,-)
dnu_fallback(Program, State, Receiver, LookupStart, Original,
             NewState, Result) :-
    allocation_state_heap(State, Heap),
    dnu_selection(Program, Heap, LookupStart, Lookup),
    finish_dnu(Program, State, Receiver, Original, Lookup, NewState, Result).

% @latex rule:DNU
% @variant allocation-state-heap
% @lean Newspeak.AllocationState.heap
% @mode allocation_state_heap(+,-)
allocation_state_heap(
    allocation_state(Heap, _NextMirror, _NextActivation, _NextClosure,
                     _NextObject, _NextClass),
    Heap).

% --------------------------------------------------------------------------
% Request resolution and completion
% --------------------------------------------------------------------------

% In the bridge representation, `value_selector(N)` is the canonical encoding
% of Lean's computed `valueSelector N`.  It is deliberately distinct from the
% generic `selector(Text)` constructor, so disequality remains declarative.

% @latex equation:request-resolution
% @lean Newspeak.valueSelector
% @mode canonical_value_selector(+,-)
canonical_value_selector(Arity, value_selector(Arity)).

% @latex equation:request-resolution
% @lean List.length
% @mode list_length(+,-)
list_length([], zero).

% @latex equation:request-resolution
% @lean List.length
% @mode list_length(+,-)
list_length([_Head|Tail], succ(Length)) :-
    list_length(Tail, Length).

% @latex equation:request-resolution
% @lean Newspeak.Message.arguments
% @mode message_arguments(+,-)
message_arguments(message(_Selector, Arguments), Arguments).

% @latex equation:request-resolution
% @lean Newspeak.Heap.closures
% @mode closure_at(+,+,-)
closure_at(Heap, Id, Result) :-
    heap_closures(Heap, Closures),
    store_lookup(Closures, Id, Result).

% @latex equation:request-resolution
% @lean Newspeak.ClosureDef.parameters
% @mode closure_parameters(+,-)
closure_parameters(
    closure_def(_Class, _Declaration, Parameters, _Locals, _Body,
                _DefiningActivation, _Receiver, _CapturedClass, _HomeMethod),
    Parameters).

% The complement of ClosureCall is rendered positively.  The first six
% clauses discharge the non-closure object tags; the remaining three cover a
% missing closure record, selector mismatch, and arity mismatch.

% @latex equation:request-resolution
% @variant ordinary-object
% @lean Newspeak.PrologBridge.PrologNotClosureCall.ordinaryObject
% @mode not_closure_call(+,+,+)
not_closure_call(_Heap, ordinary_object(_Id), _Message).

% @latex equation:request-resolution
% @variant class-object
% @lean Newspeak.PrologBridge.PrologNotClosureCall.classObject
% @mode not_closure_call(+,+,+)
not_closure_call(_Heap, class_object(_Id), _Message).

% @latex equation:request-resolution
% @variant mixin-object
% @lean Newspeak.PrologBridge.PrologNotClosureCall.mixinObject
% @mode not_closure_call(+,+,+)
not_closure_call(_Heap, mixin_object(_Id), _Message).

% @latex equation:request-resolution
% @variant activation-object
% @lean Newspeak.PrologBridge.PrologNotClosureCall.activationObject
% @mode not_closure_call(+,+,+)
not_closure_call(_Heap, activation_object(_Id), _Message).

% @latex equation:request-resolution
% @variant mirror-object
% @lean Newspeak.PrologBridge.PrologNotClosureCall.mirrorObject
% @mode not_closure_call(+,+,+)
not_closure_call(_Heap, mirror_object(_Id), _Message).

% @latex equation:request-resolution
% @variant actor-object
% @lean Newspeak.PrologBridge.PrologNotClosureCall.actorObject
% @mode not_closure_call(+,+,+)
not_closure_call(_Heap, actor_object(_Id), _Message).

% @latex equation:request-resolution
% @variant absent-closure
% @lean Newspeak.PrologBridge.PrologNotClosureCall.closureAbsent
% @mode not_closure_call(+,+,+)
not_closure_call(Heap, closure_object(Id), _Message) :-
    closure_at(Heap, Id, none).

% @latex equation:request-resolution
% @variant selector-mismatch
% @lean Newspeak.PrologBridge.PrologNotClosureCall.selectorMismatch
% @mode not_closure_call(+,+,+)
not_closure_call(Heap, closure_object(Id), Message) :-
    closure_at(Heap, Id, some(Closure)),
    closure_parameters(Closure, Parameters),
    list_length(Parameters, Arity),
    canonical_value_selector(Arity, Expected),
    message_selector(Message, Actual),
    dif(Actual, Expected).

% @latex equation:request-resolution
% @variant arity-mismatch
% @lean Newspeak.PrologBridge.PrologNotClosureCall.arityMismatch
% @mode not_closure_call(+,+,+)
not_closure_call(Heap, closure_object(Id), Message) :-
    closure_at(Heap, Id, some(Closure)),
    closure_parameters(Closure, Parameters),
    list_length(Parameters, ExpectedArity),
    message_arguments(Message, Arguments),
    list_length(Arguments, ActualArity),
    dif(ActualArity, ExpectedArity).

% @latex equation:request-resolution
% @variant ordinary
% @lean Newspeak.Program.ResolveRequest.ordinary
% @mode resolve_request(+,+,+,+,+,-)
resolve_request(Program, Heap, ActivationId, ordinary_request(Receiver),
                Message, Result) :-
    not_closure_call(Heap, Receiver, Message),
    ordinary_dispatch(Program, Heap, Receiver, Message, Result).

% @latex equation:request-resolution
% @variant implicit
% @lean Newspeak.Program.ResolveRequest.implicit
% @mode resolve_request(+,+,+,+,+,-)
resolve_request(Program, Heap, ActivationId,
                implicit_request(Annotation, Immediate), Message, Result) :-
    implicit_dispatch(Program, Heap, ActivationId, Immediate, Annotation,
                      Message, Result).

% @latex equation:request-resolution
% @variant outer
% @lean Newspeak.Program.ResolveRequest.outer
% @mode resolve_request(+,+,+,+,+,-)
resolve_request(Program, Heap, ActivationId,
                outer_request(Target, Immediate), Message, Result) :-
    outer_dispatch(Program, Heap, ActivationId, Target, Immediate,
                   Message, Result).

% @latex equation:request-resolution
% @variant self
% @lean Newspeak.Program.ResolveRequest.self
% @mode resolve_request(+,+,+,+,+,-)
resolve_request(Program, Heap, ActivationId, self_request(Immediate),
                Message, Result) :-
    self_dispatch(Program, Heap, ActivationId, Immediate, Message, Result).

% @latex equation:request-resolution
% @variant super
% @lean Newspeak.Program.ResolveRequest.super
% @mode resolve_request(+,+,+,+,+,-)
resolve_request(Program, Heap, ActivationId, super_request, Message, Result) :-
    super_dispatch(Program, Heap, ActivationId, Message, Result).

% @latex rule:Resolve
% @variant complete-invoke
% @lean Newspeak.Program.CompleteRequest.invoke
% @mode complete_request(+,+,+,+,+,-,-)
complete_request(Program, State, ActivationId, Request, Message,
                 State,
                 invoke(Method, Receiver, DefiningClass, Message)) :-
    allocation_state_heap(State, Heap),
    resolve_request(Program, Heap, ActivationId, Request, Message,
                    invoke(Method, Receiver, DefiningClass, Message)).

% @latex rule:Resolve
% @variant complete-invalid-super
% @lean Newspeak.Program.CompleteRequest.invalidSuper
% @mode complete_request(+,+,+,+,+,-,-)
complete_request(Program, State, ActivationId, Request, Message,
                 State, invalid_super(CurrentClass)) :-
    allocation_state_heap(State, Heap),
    resolve_request(Program, Heap, ActivationId, Request, Message,
                    invalid_super(CurrentClass)).

% @latex rule:DNU
% @variant complete-missing
% @lean Newspeak.Program.CompleteRequest.dnu
% @mode complete_request(+,+,+,+,+,-,-)
complete_request(Program, State, ActivationId, Request, Message,
                 NewState, Result) :-
    allocation_state_heap(State, Heap),
    resolve_request(Program, Heap, ActivationId, Request, Message,
                    missing(Receiver, LookupStart, Message)),
    class_chain(Program, Heap, LookupStart, _Chain),
    dnu_fallback(Program, State, Receiver, LookupStart, Message,
                 NewState, Result).

% --------------------------------------------------------------------------
% Method activation allocation and invocation
% --------------------------------------------------------------------------

% @latex equation:program-definition
% @lean Newspeak.Program.activationClass
% @mode activation_class(+,-)
activation_class(Program, Class) :-
    program_field(Program, activation_class, Class).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.identity
% @mode method_identity(+,-)
method_identity(
    method_def(Identity, _Activation, _Selector, _Access,
               _Parameters, _Locals, _Owner, _Body),
    Identity).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.activationDeclaration
% @mode method_activation_declaration(+,-)
method_activation_declaration(
    method_def(_Identity, Activation, _Selector, _Access,
               _Parameters, _Locals, _Owner, _Body),
    Activation).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.selector
% @mode method_selector(+,-)
method_selector(
    method_def(_Identity, _Activation, Selector, _Access,
               _Parameters, _Locals, _Owner, _Body),
    Selector).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.parameters
% @mode method_parameters(+,-)
method_parameters(
    method_def(_Identity, _Activation, _Selector, _Access,
               Parameters, _Locals, _Owner, _Body),
    Parameters).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.locals
% @mode method_local_slots(+,-)
method_local_slots(
    method_def(_Identity, _Activation, _Selector, _Access,
               _Parameters, Locals, _Owner, _Body),
    Locals).

% @latex equation:method-projections
% @lean Newspeak.MethodDef.owner
% @mode method_owner(+,-)
method_owner(
    method_def(_Identity, _Activation, _Selector, _Access,
               _Parameters, _Locals, Owner, _Body),
    Owner).

% @latex equation:method-activation
% @lean Newspeak.bindParameters
% @mode bind_parameters(+,+,-)
bind_parameters([Parameter|Parameters], [Argument|Arguments], Store) :-
    bind_parameters(Parameters, Arguments, TailStore),
    store_install(TailStore, Parameter, Argument, Store).

% @latex equation:method-activation
% @variant parameters-exhausted
% @lean Newspeak.bindParameters
% @mode bind_parameters(+,+,-)
bind_parameters([], _Arguments, store([])).

% @latex equation:method-activation
% @variant arguments-exhausted
% @lean Newspeak.bindParameters
% @mode bind_parameters(+,+,-)
bind_parameters([_Parameter|_Parameters], [], store([])).

% @latex equation:method-activation
% @lean Newspeak.initializeLocalCells
% @mode initialize_local_cells(+,-)
initialize_local_cells([], store([])).

% @latex equation:method-activation
% @lean Newspeak.initializeLocalCells
% @mode initialize_local_cells(+,-)
initialize_local_cells([Local|Locals], Store) :-
    initialize_local_cells(Locals, TailStore),
    store_install(TailStore, Local, uninitialized, Store).

% @latex equation:method-activation
% @lean Newspeak.methodActivationScopes
% @mode method_activation_scopes(+,+,-)
method_activation_scopes(Method, ActivationId, Store) :-
    method_activation_declaration(Method, Declaration),
    store_install(store([]), Declaration, ActivationId, Store).

% @latex equation:method-activation
% @variant named-class-owner
% @lean Newspeak.methodObjectLiteralScopes
% @mode method_object_literal_scopes(+,+,-)
method_object_literal_scopes(Method, _Receiver, store([])) :-
    method_owner(Method, named_class(_Declaration)).

% @latex equation:method-activation
% @variant object-literal-owner
% @lean Newspeak.methodObjectLiteralScopes
% @mode method_object_literal_scopes(+,+,-)
method_object_literal_scopes(Method, Receiver, Store) :-
    method_owner(Method, object_literal(Declaration)),
    store_install(store([]), Declaration, Receiver, Store).

% @latex equation:method-activation
% @lean Newspeak.Program.methodActivationDefinition
% @mode method_activation_definition(+,+,+,+,+,+,+,-)
method_activation_definition(Program, ActivationId, Method, Receiver,
                             DefiningClass, Message, Continuation,
                             activation_def(
                                 ActivationClass,
                                 method_provenance(Identity),
                                 Parameters, Locals, Receiver,
                                 some(DefiningClass), Continuation,
                                 some(ActivationId), true,
                                 ActivationScopes,
                                 ObjectLiteralScopes)) :-
    activation_class(Program, ActivationClass),
    method_identity(Method, Identity),
    method_parameters(Method, FormalParameters),
    message_arguments(Message, Arguments),
    bind_parameters(FormalParameters, Arguments, Parameters),
    method_local_slots(Method, LocalSlots),
    initialize_local_cells(LocalSlots, Locals),
    method_activation_scopes(Method, ActivationId, ActivationScopes),
    method_object_literal_scopes(Method, Receiver, ObjectLiteralScopes).

% @latex equation:method-activation
% @lean Newspeak.Heap.installActivation
% @mode heap_install_activation(+,+,+,-)
heap_install_activation(heap(Fields), Id, Activation, heap(NewFields)) :-
    store_lookup(Fields, activations, some(Activations)),
    store_install(Activations, Id, Activation, NewActivations),
    store_install(Fields, activations, NewActivations, NewFields).

% @latex equation:method-activation
% @lean Newspeak.Program.allocateMethodActivation
% @mode allocate_method_activation(+,+,+,+,+,+,+,-,-)
allocate_method_activation(
    Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Method, Receiver, DefiningClass, Message, Continuation,
    allocation_state(NewHeap, NextMirror, succ(NextActivation), NextClosure,
                     NextObject, NextClass),
    activation_id(NextActivation)) :-
    method_activation_definition(
        Program, activation_id(NextActivation), Method, Receiver,
        DefiningClass, Message, Continuation, Activation),
    heap_install_activation(
        Heap, activation_id(NextActivation), Activation, NewHeap).

% @latex equation:program-definition
% @lean Newspeak.Program.methodLocals
% @mode program_method_locals(+,+,-)
program_method_locals(Program, MethodId, Locals) :-
    program_field(Program, method_locals, MethodLocals),
    store_lookup(MethodLocals, MethodId, some(Locals)).

% @latex equation:program-definition
% @lean Newspeak.Program.methodBodies
% @mode program_method_body(+,+,-)
program_method_body(Program, MethodId, Body) :-
    program_field(Program, method_bodies, MethodBodies),
    store_lookup(MethodBodies, MethodId, some(Body)).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.continuation
% @mode activation_continuation(+,-)
activation_continuation(
    activation_def(_ObjectClass, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, Continuation, _HomeMethod,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Continuation).

% @latex equation:callee-continuation
% @variant non-tail
% @lean Newspeak.Program.CalleeContinuation.nonTail
% @mode callee_continuation(+,+,+,-)
callee_continuation(
    _Heap, Current, eval_stack_push(_Frames, _TopFrame), some(Current)).

% @latex equation:callee-continuation
% @variant tail
% @lean Newspeak.Program.CalleeContinuation.tail
% @mode callee_continuation(+,+,+,-)
callee_continuation(Heap, Current, eval_stack_empty, Continuation) :-
    activation_at(Heap, Current, some(Activation)),
    activation_continuation(Activation, Continuation).

% @latex rule:Invoke-NonTail
% @lean Newspeak.Program.MethodInvocationStep.nonTail
% @mode method_invocation_step(+,+,-)
method_invocation_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current, eval_stack_push(Frames, TopFrame))),
        invoke(Method, Receiver, DefiningClass, Message)),
    sequential_config(
        NewState,
        activation_stack_push(
            activation_stack_push(
                Rest,
                activation_frame(
                    Current, eval_stack_push(Frames, TopFrame))),
            activation_frame(NewActivation, eval_stack_empty)),
        initialize(NewActivation, Locals, Body, method_body(Receiver)))) :-
    method_selector(Method, Selector),
    message_selector(Message, Selector),
    method_parameters(Method, Parameters),
    message_arguments(Message, Arguments),
    list_length(Parameters, Arity),
    list_length(Arguments, Arity),
    method_identity(Method, MethodId),
    program_method_locals(Program, MethodId, Locals),
    program_method_body(Program, MethodId, Body),
    allocate_method_activation(
        Program, State, Method, Receiver, DefiningClass, Message,
        some(Current), NewState, NewActivation).

% @latex rule:Invoke-Tail
% @lean Newspeak.Program.MethodInvocationStep.tail
% @mode method_invocation_step(+,+,-)
method_invocation_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest, activation_frame(Current, eval_stack_empty)),
        invoke(Method, Receiver, DefiningClass, Message)),
    sequential_config(
        NewState,
        activation_stack_push(
            Rest, activation_frame(NewActivation, eval_stack_empty)),
        initialize(NewActivation, Locals, Body, method_body(Receiver)))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(CurrentActivation)),
    activation_continuation(CurrentActivation, Continuation),
    method_selector(Method, Selector),
    message_selector(Message, Selector),
    method_parameters(Method, Parameters),
    message_arguments(Message, Arguments),
    list_length(Parameters, Arity),
    list_length(Arguments, Arity),
    method_identity(Method, MethodId),
    program_method_locals(Program, MethodId, Locals),
    program_method_body(Program, MethodId, Body),
    allocate_method_activation(
        Program, State, Method, Receiver, DefiningClass, Message,
        Continuation, NewState, NewActivation).

% @latex rule:Resolve
% @variant machine-invoke
% @lean Newspeak.Program.RequestCompletionStep.invoke
% @mode request_completion_step(+,+,-)
request_completion_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest, activation_frame(Current, Frames)),
        dispatch(Request, Message)),
    sequential_config(
        NewState,
        activation_stack_push(
            Rest, activation_frame(Current, Frames)),
        invoke(Method, Receiver, DefiningClass, FinalMessage))) :-
    complete_request(
        Program, State, Current, Request, Message, NewState,
        invoke(Method, Receiver, DefiningClass, FinalMessage)).

% @latex rule:Resolve
% @variant machine-invalid-super
% @lean Newspeak.Program.RequestCompletionStep.invalidSuper
% @mode request_completion_step(+,+,-)
request_completion_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest, activation_frame(Current, Frames)),
        dispatch(Request, Message)),
    sequential_config(
        State,
        activation_stack_push(
            Rest, activation_frame(Current, Frames)),
        runtime_error(invalid_super(CurrentClass)))) :-
    complete_request(
        Program, State, Current, Request, Message, State,
        invalid_super(CurrentClass)).

% --------------------------------------------------------------------------
% Closure construction, dispatch, and invocation
% --------------------------------------------------------------------------

% @latex equation:program-definition
% @lean Newspeak.Program.closureClass
% @mode closure_class(+,-)
closure_class(Program, Class) :-
    program_field(Program, closure_class, Class).

% @latex equation:program-definition
% @lean Newspeak.Program.closureParameters
% @mode program_closure_parameters(+,+,-)
program_closure_parameters(Program, Declaration, Parameters) :-
    program_field(Program, closure_parameters, ParameterMap),
    store_lookup(ParameterMap, Declaration, some(Parameters)).

% @latex equation:program-definition
% @lean Newspeak.Program.closureLocals
% @mode program_closure_locals(+,+,-)
program_closure_locals(Program, Declaration, Locals) :-
    program_field(Program, closure_locals, LocalMap),
    store_lookup(LocalMap, Declaration, some(Locals)).

% @latex equation:program-definition
% @lean Newspeak.Program.closureBodies
% @mode program_closure_body(+,+,-)
program_closure_body(Program, Declaration, Body) :-
    program_field(Program, closure_bodies, BodyMap),
    store_lookup(BodyMap, Declaration, some(Body)).

% @latex equation:home-activation
% @variant top
% @lean Newspeak.ActivationDef.effectiveHome
% @mode effective_home(+,+,-)
effective_home(_Id,
    activation_def(_Class, top_provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    none).

% @latex equation:home-activation
% @variant method
% @lean Newspeak.ActivationDef.effectiveHome
% @mode effective_home(+,+,-)
effective_home(Id,
    activation_def(_Class, method_provenance(_Method), _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    some(Id)).

% @latex equation:home-activation
% @variant closure
% @lean Newspeak.ActivationDef.effectiveHome
% @mode effective_home(+,+,-)
effective_home(_Id,
    activation_def(_Class, closure_provenance(_Declaration),
                   _Parameters, _Locals, _Receiver, _CurrentClass,
                   _Continuation, Home, _Continuable,
                   _ActivationScopes, _ObjectLiteralScopes),
    Home).

% @latex equation:home-activation
% @variant initializer
% @lean Newspeak.ActivationDef.effectiveHome
% @mode effective_home(+,+,-)
effective_home(Id,
    activation_def(_Class, initializer_provenance(_Declaration),
                   _Parameters, _Locals, _Receiver, _CurrentClass,
                   _Continuation, _Home, _Continuable,
                   _ActivationScopes, _ObjectLiteralScopes),
    some(Id)).

% @latex rule:Closure-New
% @variant definition
% @lean Newspeak.Program.closureDefinition
% @mode closure_definition(+,+,+,+,+,-)
closure_definition(
    Program, DefiningId, Defining, Declaration, Body,
    closure_def(ClosureClass, Declaration, Parameters, Locals, Body,
                DefiningId, Receiver, CurrentClass, Home)) :-
    closure_class(Program, ClosureClass),
    program_closure_parameters(Program, Declaration, Parameters),
    program_closure_locals(Program, Declaration, Locals),
    activation_receiver(Defining, Receiver),
    activation_current_class(Defining, CurrentClass),
    effective_home(DefiningId, Defining, Home).

% @latex equation:request-construction
% @lean Newspeak.cascadeReceiverReference
% @mode cascade_receiver_reference(+,-)
cascade_receiver_reference(
    cascade_descriptor(ClosureDeclaration, _ReceiverParameter,
                       ReceiverSelector, ImmediateClass),
    implicit_send(ReceiverSelector, [],
                  some(activation_decl(ClosureDeclaration)),
                  ImmediateClass)).

% @latex equation:request-construction
% @lean Newspeak.cascadeStatements
% @mode cascade_statements(+,+,-)
cascade_statements(_Descriptor, [], []).

% @latex equation:request-construction
% @lean Newspeak.cascadeStatements
% @mode cascade_statements(+,+,-)
cascade_statements(Descriptor, [pair(Selector, Arguments)|Clauses],
                   [expression_statement(
                       ordinary_send(Receiver, Selector, Arguments))|Body]) :-
    cascade_receiver_reference(Descriptor, Receiver),
    cascade_statements(Descriptor, Clauses, Body).

% @latex rule:Closure-New
% @variant cascade-definition
% @lean Newspeak.Program.cascadeClosureDefinition
% @mode cascade_closure_definition(+,+,+,+,+,-)
cascade_closure_definition(
    Program, DefiningId, Defining,
    cascade_descriptor(ClosureDeclaration, ReceiverParameter,
                       _ReceiverSelector, _ImmediateClass),
    Clauses,
    closure_def(ClosureClass, ClosureDeclaration, [ReceiverParameter], [],
                Body, DefiningId, Receiver, CurrentClass, Home)) :-
    closure_class(Program, ClosureClass),
    cascade_statements(
        cascade_descriptor(ClosureDeclaration, ReceiverParameter,
                           _ReceiverSelector, _ImmediateClass),
        Clauses, Body),
    activation_receiver(Defining, Receiver),
    activation_current_class(Defining, CurrentClass),
    effective_home(DefiningId, Defining, Home).

% @latex rule:Closure-New
% @variant heap-install
% @lean Newspeak.Heap.installClosure
% @mode heap_install_closure(+,+,+,-)
heap_install_closure(heap(Fields), Id, Closure, heap(NewFields)) :-
    store_lookup(Fields, closures, some(Closures)),
    store_install(Closures, Id, Closure, NewClosures),
    store_install(Fields, closures, NewClosures, NewFields).

% @latex rule:Closure-New
% @variant allocation
% @lean Newspeak.Program.allocateClosureObject
% @mode allocate_closure_object(+,+,+,-,-)
allocate_closure_object(
    _Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Closure,
    allocation_state(NewHeap, NextMirror, NextActivation, succ(NextClosure),
                     NextObject, NextClass),
    closure_id(NextClosure)) :-
    heap_install_closure(Heap, closure_id(NextClosure), Closure, NewHeap).

% @latex rule:Closure-New
% @lean Newspeak.Program.ClosureCreationStep.create
% @mode closure_creation_step(+,+,-)
closure_creation_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(closure_literal(Declaration))),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(closure_object(NewClosure)))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Defining)),
    program_closure_body(Program, Declaration, Body),
    closure_definition(Program, Current, Defining, Declaration, Body, Closure),
    allocate_closure_object(Program, State, Closure, NewState, NewClosure).

% @latex rule:Closure-New
% @variant cascade
% @lean Newspeak.Program.ClosureCreationStep.createCascade
% @mode closure_creation_step(+,+,-)
closure_creation_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(cascade_closure(Descriptor, Clauses))),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(closure_object(NewClosure)))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Defining)),
    cascade_closure_definition(
        Program, Current, Defining, Descriptor, Clauses, Closure),
    allocate_closure_object(Program, State, Closure, NewState, NewClosure).

% @latex rule:Closure-Value
% @lean Newspeak.Program.ClosureDispatchStep.value
% @mode closure_dispatch_step(+,+,-)
closure_dispatch_step(
    _Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(ordinary_request(closure_object(Id)), Message)),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        invoke_closure(Id, Message))) :-
    allocation_state_heap(State, Heap),
    closure_at(Heap, Id, some(Closure)),
    closure_parameters(Closure, Parameters),
    list_length(Parameters, Arity),
    canonical_value_selector(Arity, Selector),
    message_selector(Message, Selector),
    message_arguments(Message, Arguments),
    list_length(Arguments, Arity).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.locals
% @mode closure_locals(+,-)
closure_locals(
    closure_def(_Class, _Declaration, _Parameters, Locals, _Body,
                _DefiningActivation, _Receiver, _CapturedClass, _HomeMethod),
    Locals).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.body
% @mode closure_body(+,-)
closure_body(
    closure_def(_Class, _Declaration, _Parameters, _Locals, Body,
                _DefiningActivation, _Receiver, _CapturedClass, _HomeMethod),
    Body).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.definingActivation
% @mode closure_defining_activation(+,-)
closure_defining_activation(
    closure_def(_Class, _Declaration, _Parameters, _Locals, _Body,
                DefiningActivation, _Receiver, _CapturedClass, _HomeMethod),
    DefiningActivation).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclaration.slot
% @mode local_declaration_slot(+,-)
local_declaration_slot(immutable_local(Slot, _Initializer), Slot).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclaration.slot
% @mode local_declaration_slot(+,-)
local_declaration_slot(mutable_initialized_local(Slot, _Initializer), Slot).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclaration.slot
% @mode local_declaration_slot(+,-)
local_declaration_slot(mutable_uninitialized_local(Slot), Slot).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclaration.slot
% @mode local_declaration_slot(+,-)
local_declaration_slot(lazy_immutable_local(Slot, _Initializer), Slot).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclaration.slot
% @mode local_declaration_slot(+,-)
local_declaration_slot(lazy_mutable_local(Slot, _Initializer), Slot).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclarationGroup.slots
% @mode local_declaration_slots(+,-)
local_declaration_slots([], []).

% @latex equation:closure-activation
% @lean Newspeak.LocalDeclarationGroup.slots
% @mode local_declaration_slots(+,-)
local_declaration_slots([Declaration|Declarations], [Slot|Slots]) :-
    local_declaration_slot(Declaration, Slot),
    local_declaration_slots(Declarations, Slots).

% @latex equation:closure-activation
% @variant sequential
% @lean Newspeak.LocalDeclarationGroup.slots
% @mode local_group_slots(+,-)
local_group_slots(sequential_local(Declaration), [Slot]) :-
    local_declaration_slot(Declaration, Slot).

% @latex equation:closure-activation
% @variant simultaneous
% @lean Newspeak.LocalDeclarationGroup.slots
% @mode local_group_slots(+,-)
local_group_slots(simultaneous_locals(Declarations), Slots) :-
    local_declaration_slots(Declarations, Slots).

% @latex equation:closure-activation
% @lean Newspeak.PrologBridge.PrologListAppend.nil
% @mode list_append(+,+,-)
list_append([], Right, Right).

% @latex equation:closure-activation
% @lean Newspeak.PrologBridge.PrologListAppend.cons
% @mode list_append(+,+,-)
list_append([Head|Left], Right, [Head|Result]) :-
    list_append(Left, Right, Result).

% @latex equation:closure-activation
% @lean Newspeak.localSlots
% @mode local_slots(+,-)
local_slots([], []).

% @latex equation:closure-activation
% @lean Newspeak.localSlots
% @mode local_slots(+,-)
local_slots([Group|Groups], Slots) :-
    local_group_slots(Group, HeadSlots),
    local_slots(Groups, TailSlots),
    list_append(HeadSlots, TailSlots, Slots).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.activationScopes
% @mode activation_scopes(+,-)
activation_scopes(
    activation_def(_Class, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, ActivationScopes, _ObjectLiteralScopes),
    ActivationScopes).

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.objectLiteralScopes
% @mode activation_object_literal_scopes(+,-)
activation_object_literal_scopes(
    activation_def(_Class, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, _ActivationScopes, ObjectLiteralScopes),
    ObjectLiteralScopes).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.declaration
% @mode closure_declaration(+,-)
closure_declaration(
    closure_def(_Class, Declaration, _Parameters, _Locals, _Body,
                _DefiningActivation, _Receiver, _CapturedClass, _HomeMethod),
    Declaration).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.capturedReceiver
% @mode closure_receiver(+,-)
closure_receiver(
    closure_def(_Class, _Declaration, _Parameters, _Locals, _Body,
                _DefiningActivation, Receiver, _CapturedClass, _HomeMethod),
    Receiver).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.capturedClass
% @mode closure_captured_class(+,-)
closure_captured_class(
    closure_def(_Class, _Declaration, _Parameters, _Locals, _Body,
                _DefiningActivation, _Receiver, CapturedClass, _HomeMethod),
    CapturedClass).

% @latex equation:closure-invocation-data
% @lean Newspeak.ClosureDef.homeMethod
% @mode closure_home_method(+,-)
closure_home_method(
    closure_def(_Class, _Declaration, _Parameters, _Locals, _Body,
                _DefiningActivation, _Receiver, _CapturedClass, HomeMethod),
    HomeMethod).

% @latex equation:closure-activation
% @lean Newspeak.Program.closureActivationDefinition
% @mode closure_activation_definition(+,+,+,+,+,+,-)
closure_activation_definition(
    Program, NewId, Closure, Defining, Message, Continuation,
    activation_def(ActivationClass, closure_provenance(Declaration),
                   Parameters, Locals, Receiver, CapturedClass,
                   Continuation, HomeMethod, true,
                   ExtendedScopes, ObjectLiteralScopes)) :-
    activation_class(Program, ActivationClass),
    closure_declaration(Closure, Declaration),
    closure_parameters(Closure, FormalParameters),
    message_arguments(Message, Arguments),
    bind_parameters(FormalParameters, Arguments, Parameters),
    closure_locals(Closure, LocalGroups),
    local_slots(LocalGroups, LocalSlots),
    initialize_local_cells(LocalSlots, Locals),
    closure_receiver(Closure, Receiver),
    closure_captured_class(Closure, CapturedClass),
    closure_home_method(Closure, HomeMethod),
    activation_scopes(Defining, BaseScopes),
    store_install(BaseScopes, Declaration, NewId, ExtendedScopes),
    activation_object_literal_scopes(Defining, ObjectLiteralScopes).

% @latex equation:closure-activation
% @lean Newspeak.Program.allocateClosureActivation
% @mode allocate_closure_activation(+,+,+,+,+,+,-,-)
allocate_closure_activation(
    Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Closure, Defining, Message, Continuation,
    allocation_state(NewHeap, NextMirror, succ(NextActivation), NextClosure,
                     NextObject, NextClass),
    activation_id(NextActivation)) :-
    closure_activation_definition(
        Program, activation_id(NextActivation), Closure, Defining, Message,
        Continuation, Activation),
    heap_install_activation(
        Heap, activation_id(NextActivation), Activation, NewHeap).

% @latex rule:Closure-Invoke-NonTail
% @lean Newspeak.Program.ClosureInvocationStep.nonTail
% @mode closure_invocation_step(+,+,-)
closure_invocation_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest, activation_frame(
                Current, eval_stack_push(Frames, TopFrame))),
        invoke_closure(Id, Message)),
    sequential_config(
        NewState,
        activation_stack_push(
            activation_stack_push(
                Rest, activation_frame(
                    Current, eval_stack_push(Frames, TopFrame))),
            activation_frame(NewActivation, eval_stack_empty)),
        initialize(NewActivation, Locals, Body, closure_body))) :-
    allocation_state_heap(State, Heap),
    closure_at(Heap, Id, some(Closure)),
    closure_defining_activation(Closure, DefiningId),
    activation_at(Heap, DefiningId, some(Defining)),
    closure_parameters(Closure, Parameters),
    message_arguments(Message, Arguments),
    list_length(Parameters, Arity),
    list_length(Arguments, Arity),
    canonical_value_selector(Arity, Selector),
    message_selector(Message, Selector),
    closure_locals(Closure, Locals),
    closure_body(Closure, Body),
    allocate_closure_activation(
        Program, State, Closure, Defining, Message, some(Current),
        NewState, NewActivation).

% @latex rule:Closure-Invoke-Tail
% @lean Newspeak.Program.ClosureInvocationStep.tail
% @mode closure_invocation_step(+,+,-)
closure_invocation_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest, activation_frame(Current, eval_stack_empty)),
        invoke_closure(Id, Message)),
    sequential_config(
        NewState,
        activation_stack_push(
            Rest, activation_frame(NewActivation, eval_stack_empty)),
        initialize(NewActivation, Locals, Body, closure_body))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Caller)),
    closure_at(Heap, Id, some(Closure)),
    closure_defining_activation(Closure, DefiningId),
    activation_at(Heap, DefiningId, some(Defining)),
    closure_parameters(Closure, Parameters),
    message_arguments(Message, Arguments),
    list_length(Parameters, Arity),
    list_length(Arguments, Arity),
    canonical_value_selector(Arity, Selector),
    message_selector(Message, Selector),
    activation_continuation(Caller, Continuation),
    closure_locals(Closure, Locals),
    closure_body(Closure, Body),
    allocate_closure_activation(
        Program, State, Closure, Defining, Message, Continuation,
        NewState, NewActivation).

% @latex equation:configuration
% @variant closure-creation
% @lean Newspeak.Program.ClosureMachineStep.creation
% @mode closure_machine_step(+,+,-)
closure_machine_step(Program, Before, After) :-
    closure_creation_step(Program, Before, After).

% @latex equation:configuration
% @variant closure-dispatch
% @lean Newspeak.Program.ClosureMachineStep.dispatch
% @mode closure_machine_step(+,+,-)
closure_machine_step(Program, Before, After) :-
    closure_dispatch_step(Program, Before, After).

% @latex equation:configuration
% @variant closure-invocation
% @lean Newspeak.Program.ClosureMachineStep.invocation
% @mode closure_machine_step(+,+,-)
closure_machine_step(Program, Before, After) :-
    closure_invocation_step(Program, Before, After).

% --------------------------------------------------------------------------
% Expression and message evaluation order
% --------------------------------------------------------------------------

% The four non-ordinary surface forms determine their request without first
% evaluating a receiver.  The pending_send record keeps the selector and
% unevaluated argument list together with that request.

% @latex equation:request-construction
% @variant implicit
% @lean Newspeak.nonOrdinaryRequest
% @mode non_ordinary_request(+,-)
non_ordinary_request(
    implicit_send(Selector, Arguments, Annotation, Immediate),
    pending_send(implicit_request(Annotation, Immediate), Selector,
                 Arguments)).

% @latex equation:request-construction
% @variant self
% @lean Newspeak.nonOrdinaryRequest
% @mode non_ordinary_request(+,-)
non_ordinary_request(
    self_send(Selector, Arguments, Immediate),
    pending_send(self_request(Immediate), Selector, Arguments)).

% @latex equation:request-construction
% @variant outer
% @lean Newspeak.nonOrdinaryRequest
% @mode non_ordinary_request(+,-)
non_ordinary_request(
    outer_send(Selector, Arguments, Target, Immediate),
    pending_send(outer_request(Target, Immediate), Selector, Arguments)).

% @latex equation:request-construction
% @variant super
% @lean Newspeak.nonOrdinaryRequest
% @mode non_ordinary_request(+,-)
non_ordinary_request(
    super_send(Selector, Arguments),
    pending_send(super_request, Selector, Arguments)).

% @latex rule:Send-No-Args
% @lean Newspeak.startPendingSend
% @mode start_pending_send(+,+,+,+,+,-)
start_pending_send(
    State, Rest, Current, Frames,
    pending_send(Request, Selector, []),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(Request, message(Selector, [])))).

% @latex rule:Send-First-Arg
% @lean Newspeak.startPendingSend
% @mode start_pending_send(+,+,+,+,+,-)
start_pending_send(
    State, Rest, Current, Frames,
    pending_send(Request, Selector, [First|Remaining]),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    arguments(Request, Selector, [], Remaining)))),
        evaluate(First))).

% @latex equation:receiver-continuations
% @variant no-arguments
% @lean Newspeak.continueReceiver
% @mode continue_receiver(+,+,+,+,+,+,+,-)
continue_receiver(
    State, Rest, Current, Frames, Receiver, Selector, [],
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(ordinary_request(Receiver), message(Selector, [])))).

% @latex equation:receiver-continuations
% @variant first-argument
% @lean Newspeak.continueReceiver
% @mode continue_receiver(+,+,+,+,+,+,+,-)
continue_receiver(
    State, Rest, Current, Frames, Receiver, Selector, [First|Remaining],
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    arguments(ordinary_request(Receiver), Selector, [],
                              Remaining)))),
        evaluate(First))).

% @latex equation:async-receiver-continuations
% @variant no-arguments
% @lean Newspeak.continueEventualReceiver
% @mode continue_eventual_receiver(+,+,+,+,+,+,+,-)
continue_eventual_receiver(
    State, Rest, Current, Frames, Receiver, Selector, [],
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(eventual_request(Receiver), message(Selector, [])))).

% @latex equation:async-receiver-continuations
% @variant first-argument
% @lean Newspeak.continueEventualReceiver
% @mode continue_eventual_receiver(+,+,+,+,+,+,+,-)
continue_eventual_receiver(
    State, Rest, Current, Frames, Receiver, Selector, [First|Remaining],
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    arguments(eventual_request(Receiver), Selector, [],
                              Remaining)))),
        evaluate(First))).

% @latex equation:argument-continuations
% @variant dispatch
% @lean Newspeak.continueArguments
% @mode continue_arguments(+,+,+,+,+,+,+,+,+,-)
continue_arguments(
    State, Rest, Current, Frames, Request, Selector, Values, [], Value,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(Request, message(Selector, Accumulated)))) :-
    list_append(Values, [Value], Accumulated).

% @latex equation:argument-continuations
% @variant next-argument
% @lean Newspeak.continueArguments
% @mode continue_arguments(+,+,+,+,+,+,+,+,+,-)
continue_arguments(
    State, Rest, Current, Frames, Request, Selector, Values,
    [First|Later], Value,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    arguments(Request, Selector, Accumulated, Later)))),
        evaluate(First))) :-
    list_append(Values, [Value], Accumulated).

% @latex equation:configuration
% @variant literal-value
% @lean Newspeak.Program.ExpressionOrderStep.value
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(value(Object))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Object))).

% @latex rule:Self-Value
% @lean Newspeak.Program.ExpressionOrderStep.selfValue
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(self_value)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Receiver))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, Receiver).

% @latex rule:Send-Receiver
% @lean Newspeak.Program.ExpressionOrderStep.ordinaryReceiver
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(ordinary_send(Receiver, Selector, Arguments))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, receiver(Selector, Arguments)))),
        evaluate(Receiver))).

% @latex rule:Async-Receiver
% @lean Newspeak.Program.ExpressionOrderStep.eventualReceiver
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(eventual_send(Receiver, Selector, Arguments))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, async_receiver(Selector, Arguments)))),
        evaluate(Receiver))).

% @latex equation:request-construction
% @variant non-ordinary-step
% @lean Newspeak.Program.ExpressionOrderStep.nonOrdinary
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(Expression)),
    After) :-
    non_ordinary_request(Expression, Pending),
    start_pending_send(State, Rest, Current, Frames, Pending, After).

% @latex equation:receiver-continuations
% @variant machine-step
% @lean Newspeak.Program.ExpressionOrderStep.receiverValue
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, receiver(Selector, Arguments)))),
        object(Receiver)),
    After) :-
    continue_receiver(
        State, Rest, Current, Frames, Receiver, Selector, Arguments, After).

% @latex equation:async-receiver-continuations
% @variant machine-step
% @lean Newspeak.Program.ExpressionOrderStep.eventualReceiverValue
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, async_receiver(Selector, Arguments)))),
        object(Receiver)),
    After) :-
    continue_eventual_receiver(
        State, Rest, Current, Frames, Receiver, Selector, Arguments, After).

% @latex equation:argument-continuations
% @variant machine-step
% @lean Newspeak.Program.ExpressionOrderStep.argumentValue
% @mode expression_order_step(+,+,-)
expression_order_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    arguments(Request, Selector, Values, Remaining)))),
        object(Value)),
    After) :-
    continue_arguments(
        State, Rest, Current, Frames, Request, Selector, Values, Remaining,
        Value, After).

% Deferred messages evaluate only their arguments.  These four clauses are
% the direct relational reading of Equation (9.10).

% @latex equation:message-evaluation
% @variant start-empty
% @lean Newspeak.Program.startMessageEvaluation
% @mode start_message_evaluation(+,+,+,+,+,-)
start_message_evaluation(
    State, Rest, Current, Frames, message_template(Selector, []),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        message_value(message(Selector, [])))).

% @latex equation:message-evaluation
% @variant start-first
% @lean Newspeak.Program.startMessageEvaluation
% @mode start_message_evaluation(+,+,+,+,+,-)
start_message_evaluation(
    State, Rest, Current, Frames,
    message_template(Selector, [First|Remaining]),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    message_arguments(Selector, [], Remaining)))),
        evaluate(First))).

% @latex equation:message-evaluation
% @variant continue-finish
% @lean Newspeak.Program.continueMessageEvaluation
% @mode continue_message_evaluation(+,+,+,+,+,+,+,+,-)
continue_message_evaluation(
    State, Rest, Current, Frames, Selector, Values, [], Value,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        message_value(message(Selector, Accumulated)))) :-
    list_append(Values, [Value], Accumulated).

% @latex equation:message-evaluation
% @variant continue-next
% @lean Newspeak.Program.continueMessageEvaluation
% @mode continue_message_evaluation(+,+,+,+,+,+,+,+,-)
continue_message_evaluation(
    State, Rest, Current, Frames, Selector, Values, [First|Later], Value,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    message_arguments(Selector, Accumulated, Later)))),
        evaluate(First))) :-
    list_append(Values, [Value], Accumulated).

% @latex equation:message-evaluation
% @variant start-step
% @lean Newspeak.Program.MessageEvaluationStep.start
% @mode message_evaluation_step(+,+,-)
message_evaluation_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate_message(Template)),
    After) :-
    start_message_evaluation(State, Rest, Current, Frames, Template, After).

% @latex equation:message-evaluation
% @variant argument-step
% @lean Newspeak.Program.MessageEvaluationStep.argument
% @mode message_evaluation_step(+,+,-)
message_evaluation_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    message_arguments(Selector, Values, Remaining)))),
        object(Value)),
    After) :-
    continue_message_evaluation(
        State, Rest, Current, Frames, Selector, Values, Remaining, Value,
        After).

% --------------------------------------------------------------------------
% Simultaneous local initialization
% --------------------------------------------------------------------------

% @latex equation:program-definition
% @lean Newspeak.Program.nilObject
% @mode program_nil_object(+,-)
program_nil_object(Program, Object) :-
    program_field(Program, nil_object, Object).

% @latex equation:local-simultaneous-install
% @lean Newspeak.Program.pastFutureExpression
% @mode program_past_future_expression(+,+,-)
program_past_future_expression(Program, Activation, Expression) :-
    program_field(Program, past_future_expressions, Expressions),
    store_lookup(Expressions, Activation, some(Expression)).

% @latex equation:local-simultaneous-install
% @variant immutable
% @lean Newspeak.Program.localInstallExpression
% @mode local_install_expression(+,+,+,-)
local_install_expression(
    Program, Activation, immutable_local(Slot, Initializer),
    write_local(
        Activation, Slot,
        ordinary_send(PastFuture, selector('computing:'), [Initializer]))) :-
    program_past_future_expression(Program, Activation, PastFuture).

% @latex equation:local-simultaneous-install
% @variant mutable-initialized
% @lean Newspeak.Program.localInstallExpression
% @mode local_install_expression(+,+,+,-)
local_install_expression(
    Program, Activation, mutable_initialized_local(Slot, Initializer),
    write_local(
        Activation, Slot,
        ordinary_send(PastFuture, selector('computing:'), [Initializer]))) :-
    program_past_future_expression(Program, Activation, PastFuture).

% @latex equation:local-simultaneous-install
% @variant mutable-uninitialized
% @lean Newspeak.Program.localInstallExpression
% @mode local_install_expression(+,+,+,-)
local_install_expression(
    Program, Activation, mutable_uninitialized_local(Slot),
    write_local(Activation, Slot, value(Nil))) :-
    program_nil_object(Program, Nil).

% @latex equation:local-simultaneous-install
% @variant lazy-immutable
% @lean Newspeak.Program.localInstallExpression
% @mode local_install_expression(+,+,+,-)
local_install_expression(
    Program, Activation, lazy_immutable_local(Slot, _Initializer),
    write_local(Activation, Slot, value(Nil))) :-
    program_nil_object(Program, Nil).

% @latex equation:local-simultaneous-install
% @variant lazy-mutable
% @lean Newspeak.Program.localInstallExpression
% @mode local_install_expression(+,+,+,-)
local_install_expression(
    Program, Activation, lazy_mutable_local(Slot, _Initializer),
    write_local(Activation, Slot, value(Nil))) :-
    program_nil_object(Program, Nil).

% @latex equation:local-simultaneous-expansion
% @variant immutable-resolution
% @lean Newspeak.localResolveExpression
% @mode local_resolve_expression(+,+,-)
local_resolve_expression(
    Activation, immutable_local(Slot, _Initializer),
    some(ordinary_send(
        read_local(Activation, Slot), selector(resolve), []))).

% @latex equation:local-simultaneous-expansion
% @variant mutable-resolution
% @lean Newspeak.localResolveExpression
% @mode local_resolve_expression(+,+,-)
local_resolve_expression(
    Activation, mutable_initialized_local(Slot, _Initializer),
    some(ordinary_send(
        read_local(Activation, Slot), selector(resolve), []))).

% @latex equation:local-simultaneous-expansion
% @variant mutable-uninitialized
% @lean Newspeak.localResolveExpression
% @mode local_resolve_expression(+,+,-)
local_resolve_expression(
    _Activation, mutable_uninitialized_local(_Slot), none).

% @latex equation:local-simultaneous-expansion
% @variant lazy-immutable
% @lean Newspeak.localResolveExpression
% @mode local_resolve_expression(+,+,-)
local_resolve_expression(
    _Activation, lazy_immutable_local(_Slot, _Initializer), none).

% @latex equation:local-simultaneous-expansion
% @variant lazy-mutable
% @lean Newspeak.localResolveExpression
% @mode local_resolve_expression(+,+,-)
local_resolve_expression(
    _Activation, lazy_mutable_local(_Slot, _Initializer), none).

% @latex equation:local-simultaneous-expansion
% @variant installation-list-empty
% @lean List.map
% @mode local_install_expressions(+,+,+,-)
local_install_expressions(_Program, _Activation, [], []).

% @latex equation:local-simultaneous-expansion
% @variant installation-list-cons
% @lean List.map
% @mode local_install_expressions(+,+,+,-)
local_install_expressions(
    Program, Activation, [Declaration|Declarations],
    [Expression|Expressions]) :-
    local_install_expression(Program, Activation, Declaration, Expression),
    local_install_expressions(
        Program, Activation, Declarations, Expressions).

% @latex equation:local-simultaneous-expansion
% @variant resolution-list-empty
% @lean List.filterMap
% @mode local_resolve_expressions(+,+,-)
local_resolve_expressions(_Activation, [], []).

% @latex equation:local-simultaneous-expansion
% @variant resolution-list-some
% @lean List.filterMap
% @mode local_resolve_expressions(+,+,-)
local_resolve_expressions(
    Activation, [Declaration|Declarations], [Expression|Expressions]) :-
    local_resolve_expression(Activation, Declaration, some(Expression)),
    local_resolve_expressions(Activation, Declarations, Expressions).

% @latex equation:local-simultaneous-expansion
% @variant resolution-list-none
% @lean List.filterMap
% @mode local_resolve_expressions(+,+,-)
local_resolve_expressions(
    Activation, [Declaration|Declarations], Expressions) :-
    local_resolve_expression(Activation, Declaration, none),
    local_resolve_expressions(Activation, Declarations, Expressions).

% @latex equation:local-simultaneous-expansion
% @lean Newspeak.Program.localSimCode
% @mode local_sim_code(+,+,+,-)
local_sim_code(Program, Activation, Declarations, Code) :-
    local_install_expressions(
        Program, Activation, Declarations, Installations),
    local_resolve_expressions(Activation, Declarations, Resolutions),
    list_append(Installations, Resolutions, Code).

% @latex equation:local-simultaneous-start
% @variant empty
% @lean Newspeak.startSimultaneousLocals
% @mode start_simultaneous_locals(+,+,+,+,+,+,+,+,+,+,-)
start_simultaneous_locals(
    Program, State, Rest, Current, Frames, Activation, Declarations,
    Remaining, Body, Target,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(Activation, Remaining, Body, Target))) :-
    local_sim_code(Program, Activation, Declarations, []).

% @latex equation:local-simultaneous-start
% @variant nonempty
% @lean Newspeak.startSimultaneousLocals
% @mode start_simultaneous_locals(+,+,+,+,+,+,+,+,+,+,-)
start_simultaneous_locals(
    Program, State, Rest, Current, Frames, Activation, Declarations,
    Remaining, Body, Target,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_locals(
                        Later, Activation, Remaining, Body, Target)))),
        evaluate(First))) :-
    local_sim_code(Program, Activation, Declarations, [First|Later]).

% --------------------------------------------------------------------------
% Local cells, body sequencing, and ordinary completion
% --------------------------------------------------------------------------

% @latex equation:heap-records
% @lean Newspeak.ActivationDef.locals
% @mode activation_locals(+,-)
activation_locals(
    activation_def(_Class, _Provenance, _Parameters, Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Locals).

% @latex equation:local-slot-operations
% @lean Newspeak.Heap.readActivationLocal
% @mode read_activation_local_value(+,+,+,-)
read_activation_local_value(Heap, Activation, Slot, Value) :-
    activation_at(Heap, Activation, some(Definition)),
    activation_locals(Definition, Locals),
    store_lookup(Locals, Slot, some(local_value(Value))).

% @latex equation:local-slot-operations
% @variant activation-local-update
% @lean Newspeak.ActivationDef
% @mode activation_with_local_value(+,+,+,-)
activation_with_local_value(
    activation_def(Class, Provenance, Parameters, Locals,
                   Receiver, CurrentClass, Continuation, Home,
                   Continuable, ActivationScopes, ObjectLiteralScopes),
    Slot, Value,
    activation_def(Class, Provenance, Parameters, NewLocals,
                   Receiver, CurrentClass, Continuation, Home,
                   Continuable, ActivationScopes, ObjectLiteralScopes)) :-
    store_lookup(Locals, Slot, some(_OldCell)),
    store_install(Locals, Slot, local_value(Value), NewLocals).

% @latex equation:local-slot-operations
% @lean Newspeak.Heap.writeActivationLocal
% @mode write_activation_local_heap(+,+,+,+,-)
write_activation_local_heap(Heap, Activation, Slot, Value, NewHeap) :-
    activation_at(Heap, Activation, some(Definition)),
    activation_with_local_value(Definition, Slot, Value, NewDefinition),
    heap_install_activation(Heap, Activation, NewDefinition, NewHeap).

% @latex rule:Finish-Resume
% @variant sever-continuation
% @lean Newspeak.Heap.severActivationContinuation
% @mode sever_activation_continuation_heap(+,+,-)
sever_activation_continuation_heap(Heap, Activation, NewHeap) :-
    activation_at(Heap, Activation, some(Definition)),
    activation_without_continuation(Definition, NewDefinition),
    heap_install_activation(Heap, Activation, NewDefinition, NewHeap).

% @latex rule:Finish-Resume
% @variant activation-update
% @lean Newspeak.ActivationDef
% @mode activation_without_continuation(+,-)
activation_without_continuation(
    activation_def(Class, Provenance, Parameters, Locals,
                   Receiver, CurrentClass, _Continuation, Home,
                   Continuable, ActivationScopes, ObjectLiteralScopes),
    activation_def(Class, Provenance, Parameters, Locals,
                   Receiver, CurrentClass, none, Home,
                   Continuable, ActivationScopes, ObjectLiteralScopes)).

% @latex equation:local-init-start
% @variant immutable
% @lean Newspeak.eagerLocalInitializer
% @mode eager_local_initializer(+,-)
eager_local_initializer(
    immutable_local(Slot, Initializer), some(pair(Slot, Initializer))).

% @latex equation:local-init-start
% @variant mutable-initialized
% @lean Newspeak.eagerLocalInitializer
% @mode eager_local_initializer(+,-)
eager_local_initializer(
    mutable_initialized_local(Slot, Initializer),
    some(pair(Slot, Initializer))).

% @latex equation:local-init-start
% @variant mutable-uninitialized
% @lean Newspeak.eagerLocalInitializer
% @mode eager_local_initializer(+,-)
eager_local_initializer(mutable_uninitialized_local(_Slot), none).

% @latex equation:local-init-start
% @variant lazy-immutable
% @lean Newspeak.eagerLocalInitializer
% @mode eager_local_initializer(+,-)
eager_local_initializer(lazy_immutable_local(_Slot, _Initializer), none).

% @latex equation:local-init-start
% @variant lazy-mutable
% @lean Newspeak.eagerLocalInitializer
% @mode eager_local_initializer(+,-)
eager_local_initializer(lazy_mutable_local(_Slot, _Initializer), none).

% @latex equation:local-init-nil
% @variant immutable
% @lean Newspeak.nilInitializedLocal
% @mode nil_initialized_local(+,-)
nil_initialized_local(immutable_local(_Slot, _Initializer), none).

% @latex equation:local-init-nil
% @variant mutable-initialized
% @lean Newspeak.nilInitializedLocal
% @mode nil_initialized_local(+,-)
nil_initialized_local(
    mutable_initialized_local(_Slot, _Initializer), none).

% @latex equation:local-init-nil
% @variant mutable-uninitialized
% @lean Newspeak.nilInitializedLocal
% @mode nil_initialized_local(+,-)
nil_initialized_local(mutable_uninitialized_local(Slot), some(Slot)).

% @latex equation:local-init-nil
% @variant lazy-immutable
% @lean Newspeak.nilInitializedLocal
% @mode nil_initialized_local(+,-)
nil_initialized_local(
    lazy_immutable_local(Slot, _Initializer), some(Slot)).

% @latex equation:local-init-nil
% @variant lazy-mutable
% @lean Newspeak.nilInitializedLocal
% @mode nil_initialized_local(+,-)
nil_initialized_local(
    lazy_mutable_local(Slot, _Initializer), some(Slot)).

% @latex equation:body-results
% @variant empty-method
% @lean Newspeak.emptyBodyResult
% @mode empty_body_result(+,+,-)
empty_body_result(_Program, method_body(Receiver), Receiver).

% @latex equation:body-results
% @variant empty-closure
% @lean Newspeak.emptyBodyResult
% @mode empty_body_result(+,+,-)
empty_body_result(Program, closure_body, Nil) :-
    program_nil_object(Program, Nil).

% @latex equation:body-results
% @variant last-method
% @lean Newspeak.lastBodyResult
% @mode last_body_result(+,+,-)
last_body_result(method_body(Receiver), _Value, Receiver).

% @latex equation:body-results
% @variant last-closure
% @lean Newspeak.lastBodyResult
% @mode last_body_result(+,+,-)
last_body_result(closure_body, Value, Value).

% @latex equation:statement-start
% @variant expression
% @lean Newspeak.startStatement
% @mode start_statement(+,+,-,-)
start_statement(Frames, expression_statement(Expression), Frames, Expression).

% @latex equation:statement-start
% @variant return
% @lean Newspeak.startStatement
% @mode start_statement(+,+,-,-)
start_statement(
    Frames, return_statement(Expression),
    eval_stack_push(Frames, return_frame), Expression).

% @latex equation:resume
% @variant empty
% @lean Newspeak.resumeActivation
% @mode resume_activation(+,+,-)
resume_activation(activation_stack_empty, _Target, none).

% @latex equation:resume
% @variant found
% @lean Newspeak.resumeActivation
% @mode resume_activation(+,+,-)
resume_activation(
    activation_stack_push(Rest, activation_frame(Target, Frames)), Target,
    some(activation_stack_push(
        Rest, activation_frame(Target, Frames)))).

% @latex equation:resume
% @variant skip
% @lean Newspeak.resumeActivation
% @mode resume_activation(+,+,-)
resume_activation(
    activation_stack_push(Rest, activation_frame(Other, _Frames)), Target,
    Result) :-
    dif(Other, Target),
    resume_activation(Rest, Target, Result).

% @latex equation:local-init-empty
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(Current, [], Body, Target)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        body(Target, Body))).

% @latex equation:local-init-start
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(
            Current, [sequential_local(Declaration)|Remaining], Body, Target)),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, initialize_local(Slot, Remaining, Body, Target)))),
        evaluate(Initializer))) :-
    eager_local_initializer(Declaration, some(pair(Slot, Initializer))).

% @latex equation:local-init-nil
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(
            Current, [sequential_local(Declaration)|Remaining], Body, Target)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(Current, Remaining, Body, Target))) :-
    eager_local_initializer(Declaration, none),
    nil_initialized_local(Declaration, some(Slot)),
    program_nil_object(Program, Nil),
    write_activation_local_heap(Heap, Current, Slot, Nil, NewHeap).

% @latex equation:local-simultaneous-start
% @variant body-machine
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(
            Current, [simultaneous_locals(Declarations)|Remaining], Body,
            Target)),
    After) :-
    start_simultaneous_locals(
        Program, State, Rest, Current, Frames, Current, Declarations,
        Remaining, Body, Target, After).

% @latex equation:local-slot-operations
% @variant read-step
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(read_local(Activation, Slot))),
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Value))) :-
    read_activation_local_value(Heap, Activation, Slot, Value).

% @latex equation:local-slot-operations
% @variant write-start
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(write_local(Activation, Slot, Expression))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, local_write(Activation, Slot)))),
        evaluate(Expression))).

% @latex equation:local-init-commit
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    initialize_local(Slot, Remaining, Body, Target)))),
        object(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(Current, Remaining, Body, Target))) :-
    write_activation_local_heap(Heap, Current, Slot, Value, NewHeap).

% @latex equation:local-slot-operations
% @variant write-commit
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, local_write(Activation, Slot)))),
        object(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Value))) :-
    write_activation_local_heap(Heap, Activation, Slot, Value, NewHeap).

% @latex equation:local-simultaneous-start
% @variant continuation-empty
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_locals([], Activation, Remaining, Body,
                                        Target)))),
        object(_Value)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize(Activation, Remaining, Body, Target))).

% @latex equation:local-simultaneous-start
% @variant continuation-next
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_locals(
                        [First|Later], Activation, Remaining, Body, Target)))),
        object(_Value)),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_locals(
                        Later, Activation, Remaining, Body, Target)))),
        evaluate(First))).

% @latex equation:statement-continuations
% @variant finish
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, sequence(Target, [])))),
        object(Value)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        finish(Result))) :-
    last_body_result(Target, Value, Result).

% @latex equation:statement-continuations
% @variant next
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, sequence(Target, [Statement|Later])))),
        object(_Value)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, NewFrames)),
        evaluate(Expression))) :-
    start_statement(
        eval_stack_push(Frames, sequence(Target, Later)), Statement,
        NewFrames, Expression).

% @latex equation:empty-body
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        body(Target, [])),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        finish(Result))) :-
    empty_body_result(Program, Target, Result).

% @latex equation:nonempty-body
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        body(Target, [Statement|Remaining])),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, NewFrames)),
        evaluate(Expression))) :-
    start_statement(
        eval_stack_push(Frames, sequence(Target, Remaining)), Statement,
        NewFrames, Expression).

% @latex rule:Finish-Halt
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        finish(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_empty,
        halt_control(Value))) :-
    activation_at(Heap, Current, some(Activation)),
    activation_continuation(Activation, none),
    sever_activation_continuation_heap(Heap, Current, NewHeap).

% @latex rule:Finish-Resume
% @lean Newspeak.Program.bodyMachineNext
% @mode body_machine_step(+,+,-)
body_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        finish(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        Resumed,
        object(Value))) :-
    activation_at(Heap, Current, some(Activation)),
    activation_continuation(Activation, some(Continuation)),
    sever_activation_continuation_heap(Heap, Current, NewHeap),
    resume_activation(
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        Continuation, some(Resumed)).

% --------------------------------------------------------------------------
% Atomic values and direct object-slot primitives
% --------------------------------------------------------------------------

% @latex equation:atom-canonicality
% @lean Newspeak.Program.atoms
% @mode program_atom_object(+,+,-)
program_atom_object(Program, Payload, Object) :-
    program_field(Program, atoms, Atoms),
    store_lookup(Atoms, Payload, some(Object)).

% @latex equation:heap-records
% @lean Newspeak.Heap.objects
% @mode object_at(+,+,-)
object_at(Heap, Object, Result) :-
    heap_objects(Heap, Objects),
    store_lookup(Objects, Object, Result).

% @latex equation:slot-operations
% @lean Newspeak.ObjectDef.slots
% @mode object_slots(+,-)
object_slots(object_def(_Class, Slots, _NestedClasses, _WeakContainer), Slots).

% @latex equation:slot-operations
% @lean Newspeak.Heap.readObjectSlot
% @mode read_object_slot_value(+,+,+,-)
read_object_slot_value(Heap, Object, Slot, Value) :-
    object_at(Heap, Object, some(Definition)),
    object_slots(Definition, Slots),
    store_lookup(Slots, Slot, some(Value)).

% @latex equation:slot-operations
% @variant object-slot-update
% @lean Newspeak.Heap.objectSlotTransform
% @mode object_with_slot_value(+,+,+,-)
object_with_slot_value(
    object_def(Class, Slots, NestedClasses, WeakContainer), Slot, Value,
    object_def(Class, NewSlots, NestedClasses, WeakContainer)) :-
    store_lookup(Slots, Slot, some(_OldValue)),
    store_install(Slots, Slot, Value, NewSlots).

% @latex equation:slot-operations
% @variant heap-install
% @lean Newspeak.Heap.installObject
% @mode heap_install_object(+,+,+,-)
heap_install_object(heap(Fields), Object, Definition, heap(NewFields)) :-
    store_lookup(Fields, objects, some(Objects)),
    store_install(Objects, Object, Definition, NewObjects),
    store_install(Fields, objects, NewObjects, NewFields).

% @latex equation:slot-operations
% @lean Newspeak.Heap.writeObjectSlot
% @mode write_object_slot_heap(+,+,+,+,-)
write_object_slot_heap(Heap, Object, Slot, Value, NewHeap) :-
    object_at(Heap, Object, some(Definition)),
    object_with_slot_value(Definition, Slot, Value, NewDefinition),
    heap_install_object(Heap, Object, NewDefinition, NewHeap).

% @latex equation:atom-canonicality
% @variant evaluation
% @lean Newspeak.Program.ObjectSlotStep.atom
% @mode object_slot_step(+,+,-)
object_slot_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(atom(Payload))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Object))) :-
    program_atom_object(Program, Payload, Object).

% @latex equation:slot-operations
% @variant read
% @lean Newspeak.Program.ObjectSlotStep.read
% @mode object_slot_step(+,+,-)
object_slot_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(read_slot(Object, Slot))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Value))) :-
    allocation_state_heap(State, Heap),
    read_object_slot_value(Heap, Object, Slot, Value).

% @latex equation:slot-operations
% @variant write-start
% @lean Newspeak.Program.ObjectSlotStep.writeStart
% @mode object_slot_step(+,+,-)
object_slot_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(write_slot(Object, Slot, Expression))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, slot_write(Object, Slot)))),
        evaluate(Expression))).

% @latex equation:slot-operations
% @variant write-commit
% @lean Newspeak.Program.ObjectSlotStep.writeCommit
% @mode object_slot_step(+,+,-)
object_slot_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, slot_write(Object, Slot)))),
        object(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Value))) :-
    write_object_slot_heap(Heap, Object, Slot, Value, NewHeap).

% --------------------------------------------------------------------------
% PEG, projection, stable identification, and front-end composition
% --------------------------------------------------------------------------

% The front end is intentionally proof carrying.  Grammar recognition and
% semantic actions are represented by their finite derivations; the clauses
% below expose exactly the phase boundaries of Section 13 without asking the
% Prolog engine to reimplement Unicode decoding or the Newspeak action map.

% @latex equation:peg-grammar-validity
% @lean Newspeak.PEGGrammarWellFormed
% @mode peg_grammar_well_formed(+,+)
peg_grammar_well_formed(
    peg_grammar_well_formed(WellFormedProof), Grammar).

% Primitive graph premises used by the structural PEG clauses.  They are
% explicit proof objects because character predicates and natural-number
% arithmetic belong to the metalanguage, not to the checked Prolog subset.

% @latex equation:peg-atomic-recognition
% @variant source-index
% @lean Newspeak.SourceText
% @mode source_character_at(+,+,+,+)
source_character_at(
    source_character_at(IndexProof), Source, Offset, Result).

% @latex equation:peg-atomic-recognition
% @variant source-index-different
% @lean Newspeak.SourceText
% @mode source_character_different(+,+,+,+)
source_character_different(
    source_character_different(DifferenceProof), Source, Offset, Character).

% @latex equation:peg-atomic-recognition
% @variant character-set-application
% @lean Newspeak.PEGExpr.characterSet
% @mode character_set_accepts(+,+,+,+)
character_set_accepts(
    character_set_accepts(ApplicationProof), Predicate, Character, Result).

% @latex equation:peg-atomic-recognition
% @variant successor
% @lean Newspeak.PEGRecognizes.characterSuccess
% @mode natural_successor(+,+,-)
natural_successor(natural_successor(SuccessorProof), Offset, Next).

% @latex equation:peg-repetition-lookahead
% @variant strict-progress
% @lean Newspeak.PEGRecognizes.starStep
% @mode natural_strictly_less(+,+,+)
natural_strictly_less(
    natural_strictly_less(ProgressProof), Smaller, Larger).

% @latex equation:peg-nonterminal-capture
% @variant grammar-rule
% @lean Newspeak.PEGGrammar.rules
% @mode peg_grammar_rule(+,+,+,+)
peg_grammar_rule(
    peg_grammar_rule(LookupProof), Grammar, Name, Result).

% @latex equation:peg-atomic-recognition
% @variant empty
% @lean Newspeak.PEGRecognizes.empty
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_empty, _Grammar, _Source, peg_empty, Offset,
    peg_success(Offset, [])).

% @latex equation:peg-atomic-recognition
% @variant character-success
% @lean Newspeak.PEGRecognizes.characterSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_character_success(PresentProof, SuccessorProof),
    _Grammar, Source, peg_character(Character), Offset,
    peg_success(Next, [concrete_leaf(Offset, Next)])) :-
    source_character_at(
        PresentProof, Source, Offset, some(Character)),
    natural_successor(SuccessorProof, Offset, Next).

% @latex equation:peg-atomic-recognition
% @variant character-failure
% @lean Newspeak.PEGRecognizes.characterFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_character_failure(DifferenceProof),
    _Grammar, Source, peg_character(Character), Offset,
    peg_failure(Offset)) :-
    source_character_different(
        DifferenceProof, Source, Offset, Character).

% @latex equation:peg-atomic-recognition
% @variant character-set-success
% @lean Newspeak.PEGRecognizes.characterSetSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_character_set_success(
        PresentProof, AcceptanceProof, SuccessorProof),
    _Grammar, Source, peg_character_set(Predicate), Offset,
    peg_success(Next, [concrete_leaf(Offset, Next)])) :-
    source_character_at(
        PresentProof, Source, Offset, some(Character)),
    character_set_accepts(
        AcceptanceProof, Predicate, Character, true),
    natural_successor(SuccessorProof, Offset, Next).

% @latex equation:peg-atomic-recognition
% @variant character-set-absent
% @lean Newspeak.PEGRecognizes.characterSetFailureAbsent
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_character_set_absent(AbsentProof),
    _Grammar, Source, peg_character_set(_Predicate), Offset,
    peg_failure(Offset)) :-
    source_character_at(AbsentProof, Source, Offset, none).

% @latex equation:peg-atomic-recognition
% @variant character-set-rejected
% @lean Newspeak.PEGRecognizes.characterSetFailureRejected
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_character_set_rejected(PresentProof, RejectionProof),
    _Grammar, Source, peg_character_set(Predicate), Offset,
    peg_failure(Offset)) :-
    source_character_at(
        PresentProof, Source, Offset, some(Character)),
    character_set_accepts(
        RejectionProof, Predicate, Character, false).

% @latex equation:peg-atomic-recognition
% @variant any-success
% @lean Newspeak.PEGRecognizes.anySuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_any_success(PresentProof, SuccessorProof),
    _Grammar, Source, peg_any, Offset,
    peg_success(Next, [concrete_leaf(Offset, Next)])) :-
    source_character_at(
        PresentProof, Source, Offset, some(_Character)),
    natural_successor(SuccessorProof, Offset, Next).

% @latex equation:peg-atomic-recognition
% @variant any-failure
% @lean Newspeak.PEGRecognizes.anyFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_any_failure(AbsentProof),
    _Grammar, Source, peg_any, Offset, peg_failure(Offset)) :-
    source_character_at(AbsentProof, Source, Offset, none).

% @latex equation:peg-nonterminal-capture
% @variant nonterminal-defined
% @lean Newspeak.PEGRecognizes.nonterminalDefined
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_nonterminal_defined(LookupProof, BodyProof),
    Grammar, Source, peg_nonterminal(Name), Offset, Result) :-
    peg_grammar_rule(LookupProof, Grammar, Name, some(Body)),
    peg_recognizes(BodyProof, Grammar, Source, Body, Offset, Result).

% @latex equation:peg-nonterminal-capture
% @variant nonterminal-undefined
% @lean Newspeak.PEGRecognizes.nonterminalUndefined
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_nonterminal_undefined(LookupProof),
    Grammar, _Source, peg_nonterminal(Name), Offset,
    peg_failure(Offset)) :-
    peg_grammar_rule(LookupProof, Grammar, Name, none).

% @latex equation:peg-sequence-choice
% @variant sequence-first-failure
% @lean Newspeak.PEGRecognizes.sequenceFirstFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_sequence_first_failure(FirstProof),
    Grammar, Source, peg_sequence(First, _Second), Offset,
    peg_failure(FailureOffset)) :-
    peg_recognizes(
        FirstProof, Grammar, Source, First, Offset,
        peg_failure(FailureOffset)).

% @latex equation:peg-sequence-choice
% @variant sequence-second-failure
% @lean Newspeak.PEGRecognizes.sequenceSecondFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_sequence_second_failure(FirstProof, SecondProof),
    Grammar, Source, peg_sequence(First, Second), Offset,
    peg_failure(FailureOffset)) :-
    peg_recognizes(
        FirstProof, Grammar, Source, First, Offset,
        peg_success(Middle, FirstForest)),
    peg_recognizes(
        SecondProof, Grammar, Source, Second, Middle,
        peg_failure(FailureOffset)).

% @latex equation:peg-sequence-choice
% @variant sequence-success
% @lean Newspeak.PEGRecognizes.sequenceSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_sequence_success(FirstProof, SecondProof),
    Grammar, Source, peg_sequence(First, Second), Offset,
    peg_success(Final, Forest)) :-
    peg_recognizes(
        FirstProof, Grammar, Source, First, Offset,
        peg_success(Middle, FirstForest)),
    peg_recognizes(
        SecondProof, Grammar, Source, Second, Middle,
        peg_success(Final, SecondForest)),
    list_append(FirstForest, SecondForest, Forest).

% @latex equation:peg-sequence-choice
% @variant choice-left
% @lean Newspeak.PEGRecognizes.choiceLeftSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_choice_left(LeftProof),
    Grammar, Source, peg_ordered_choice(First, _Second), Offset,
    peg_success(Final, Forest)) :-
    peg_recognizes(
        LeftProof, Grammar, Source, First, Offset,
        peg_success(Final, Forest)).

% @latex equation:peg-sequence-choice
% @variant choice-right
% @lean Newspeak.PEGRecognizes.choiceRight
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_choice_right(LeftProof, RightProof),
    Grammar, Source, peg_ordered_choice(First, Second), Offset, Result) :-
    peg_recognizes(
        LeftProof, Grammar, Source, First, Offset,
        peg_failure(_LeftFailure)),
    peg_recognizes(RightProof, Grammar, Source, Second, Offset, Result).

% @latex equation:peg-repetition-lookahead
% @variant star-stop
% @lean Newspeak.PEGRecognizes.starStop
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_star_stop(BodyProof),
    Grammar, Source, peg_star(Body), Offset,
    peg_success(Offset, [])) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_failure(_FailureOffset)).

% @latex equation:peg-repetition-lookahead
% @variant star-step
% @lean Newspeak.PEGRecognizes.starStep
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_star_step(BodyProof, ProgressProof, RemainingProof),
    Grammar, Source, peg_star(Body), Offset,
    peg_success(Final, Forest)) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_success(Middle, FirstForest)),
    natural_strictly_less(ProgressProof, Offset, Middle),
    peg_recognizes(
        RemainingProof, Grammar, Source, peg_star(Body), Middle,
        peg_success(Final, RemainingForest)),
    list_append(FirstForest, RemainingForest, Forest).

% @latex equation:peg-repetition-lookahead
% @variant not-ahead-success
% @lean Newspeak.PEGRecognizes.notAheadSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_not_ahead_success(BodyProof),
    Grammar, Source, peg_not_ahead(Body), Offset,
    peg_success(Offset, [])) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_failure(_FailureOffset)).

% @latex equation:peg-repetition-lookahead
% @variant not-ahead-failure
% @lean Newspeak.PEGRecognizes.notAheadFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_not_ahead_failure(BodyProof),
    Grammar, Source, peg_not_ahead(Body), Offset,
    peg_failure(Offset)) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_success(_Final, _Forest)).

% @latex equation:peg-repetition-lookahead
% @variant and-ahead-success
% @lean Newspeak.PEGRecognizes.andAheadSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_and_ahead_success(BodyProof),
    Grammar, Source, peg_and_ahead(Body), Offset,
    peg_success(Offset, [])) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_success(_Final, _Forest)).

% @latex equation:peg-repetition-lookahead
% @variant and-ahead-failure
% @lean Newspeak.PEGRecognizes.andAheadFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_and_ahead_failure(BodyProof),
    Grammar, Source, peg_and_ahead(Body), Offset,
    peg_failure(Offset)) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_failure(_FailureOffset)).

% @latex equation:peg-nonterminal-capture
% @variant capture-success
% @lean Newspeak.PEGRecognizes.captureSuccess
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_capture_success(BodyProof),
    Grammar, Source, peg_capture(Name, Body), Offset,
    peg_success(Final, [concrete_node(Name, Offset, Final, Forest)])) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_success(Final, Forest)).

% @latex equation:peg-nonterminal-capture
% @variant capture-failure
% @lean Newspeak.PEGRecognizes.captureFailure
% @mode peg_recognizes(+,+,+,+,+,-)
peg_recognizes(
    peg_capture_failure(BodyProof),
    Grammar, Source, peg_capture(Name, Body), Offset,
    peg_failure(FailureOffset)) :-
    peg_recognizes(
        BodyProof, Grammar, Source, Body, Offset,
        peg_failure(FailureOffset)).

% @latex equation:peg-complete-parse
% @variant grammar-start
% @lean Newspeak.PEGGrammar.start
% @mode peg_grammar_start(+,+,+)
peg_grammar_start(
    peg_grammar_start(StartProof), Grammar, Start).

% @latex equation:peg-complete-parse
% @variant source-length
% @lean Newspeak.SourceText
% @mode source_text_length(+,+,+)
source_text_length(source_text_length(LengthProof), Source, Length).

% @latex equation:peg-complete-parse
% @lean Newspeak.PEGCompleteParse
% @mode peg_complete_parse(+,+,+,+)
peg_complete_parse(
    peg_complete_parse(StartProof, LengthProof, RecognitionProof),
    Grammar, Source, Tree) :-
    peg_grammar_start(StartProof, Grammar, Start),
    source_text_length(LengthProof, Source, Length),
    peg_recognizes(
        RecognitionProof, Grammar, Source, peg_nonterminal(Start), 0,
        peg_success(Length, [Tree])).

% Projection graph primitives.  As above, source slicing and action execution
% remain explicit applications of the supplied semantics.

% @latex equation:ast-tree-projection
% @variant token-application
% @lean Newspeak.PEGActionSemantics.token
% @mode peg_token_application(+,+,+,+,+,+)
peg_token_application(
    peg_token_application(TokenProof),
    Semantics, Source, Start, End, Value).

% @latex equation:ast-tree-projection
% @variant source-slice
% @lean Newspeak.sourceSlice
% @mode source_slice_application(+,+,+,+,-)
source_slice_application(
    source_slice_application(SliceProof), Source, Start, End, Slice).

% @latex equation:ast-tree-projection
% @variant action-application
% @lean Newspeak.PEGActionSemantics.action
% @mode peg_action_application(+,+,+,+,+,+,+,+)
peg_action_application(
    peg_action_application(ActionProof), Semantics, Name, Start, End,
    Values, Slice, ActionResult).

% @latex equation:ast-tree-projection
% @variant emit
% @lean Newspeak.emitSemanticResult
% @mode emit_semantic_result(+,+,-,-)
emit_semantic_result(
    semantic_emit(Value), Metadata, [Value], Metadata).

% @latex equation:ast-tree-projection
% @variant erase
% @lean Newspeak.emitSemanticResult
% @mode emit_semantic_result(+,+,-,-)
emit_semantic_result(semantic_erase, Metadata, [], Metadata).

% @latex equation:ast-tree-projection
% @variant metadata
% @lean Newspeak.emitSemanticResult
% @mode emit_semantic_result(+,+,-,-)
emit_semantic_result(
    semantic_metadata(Value), Metadata, [], Extended) :-
    list_append(Metadata, [Value], Extended).

% @latex equation:ast-tree-projection
% @variant leaf
% @lean Newspeak.projectConcreteTree
% @mode project_concrete_tree(+,+,+,+,-,-)
project_concrete_tree(
    project_leaf(TokenProof), Semantics, Source,
    concrete_leaf(Start, End), [Value], []) :-
    peg_token_application(
        TokenProof, Semantics, Source, Start, End, Value).

% @latex equation:ast-tree-projection
% @variant node
% @lean Newspeak.projectConcreteTree
% @mode project_concrete_tree(+,+,+,+,-,-)
project_concrete_tree(
    project_node(ForestProof, SliceProof, ActionProof),
    Semantics, Source, concrete_node(Name, Start, End, Children),
    Values, Metadata) :-
    project_concrete_forest(
        ForestProof, Semantics, Source, Children,
        ChildValues, ChildMetadata),
    source_slice_application(SliceProof, Source, Start, End, Slice),
    peg_action_application(
        ActionProof, Semantics, Name, Start, End,
        ChildValues, Slice, some(ActionResult)),
    emit_semantic_result(
        ActionResult, ChildMetadata, Values, Metadata).

% @latex equation:ast-tree-projection
% @variant forest-empty
% @lean Newspeak.projectConcreteForest
% @mode project_concrete_forest(+,+,+,+,-,-)
project_concrete_forest(
    project_forest_empty, _Semantics, _Source, [], [], []).

% @latex equation:ast-tree-projection
% @variant forest-cons
% @lean Newspeak.projectConcreteForest
% @mode project_concrete_forest(+,+,+,+,-,-)
project_concrete_forest(
    project_forest_cons(FirstProof, RestProof),
    Semantics, Source, [Tree|Remaining], Values, Metadata) :-
    project_concrete_tree(
        FirstProof, Semantics, Source, Tree, FirstValues, FirstMetadata),
    project_concrete_forest(
        RestProof, Semantics, Source, Remaining, RestValues, RestMetadata),
    list_append(FirstValues, RestValues, Values),
    list_append(FirstMetadata, RestMetadata, Metadata).

% @latex equation:ast-tree-projection
% @lean Newspeak.PEGProjects
% @mode peg_projects(+,+,+,+,+,+)
peg_projects(
    peg_projects(ProjectionProof), Semantics, Source, Tree, Root, Metadata) :-
    project_concrete_tree(
        ProjectionProof, Semantics, Source, Tree, [Root], Metadata).

% @latex equation:ast-tree-projection
% @lean Newspeak.PEGParsesAST
% @mode peg_parses_ast(+,+,+,+,+,+)
peg_parses_ast(
    peg_parses_ast(ParseProof, ProjectionProof),
    Grammar, Semantics, Source, Root, Metadata) :-
    peg_complete_parse(ParseProof, Grammar, Source, Tree),
    peg_projects(
        ProjectionProof, Semantics, Source, Tree, Root, Metadata).

% @latex equation:source-to-annotated-core
% @variant parse-and-project
% @lean Newspeak.PEGParsesNewspeakUnit
% @mode peg_parses_newspeak_unit(+,+,+,+,+,+)
peg_parses_newspeak_unit(
    peg_parses_newspeak_unit(WellFormedProof, ParseASTProof),
    Grammar, Decoders, Source, Unit, Metadata) :-
    peg_grammar_well_formed(WellFormedProof, Grammar),
    newspeak_surface_semantics(Decoders, Semantics),
    peg_parses_ast(
        ParseASTProof, Grammar, Semantics, Source,
        compilation_unit(Unit), Metadata).

% @latex equation:peg-action-map
% @variant newspeak-semantics
% @lean Newspeak.newspeakSurfaceSemantics
% @mode newspeak_surface_semantics(+,-)
newspeak_surface_semantics(
    Decoders, newspeak_surface_semantics(Decoders)).

% Stable identification is expanded below the compilation-unit traversal.
% The traversal itself is a graph premise because it merely enumerates the
% already explicit surface AST; allocation and retention are relational.

% @latex equation:stable-ast-identification
% @variant surface-node-enumeration
% @lean Newspeak.surfaceCompilationUnitNodes
% @mode surface_compilation_unit_nodes(+,+,-)
surface_compilation_unit_nodes(
    surface_compilation_unit_nodes(EnumerationProof), Unit, Nodes).

% @latex equation:stable-ast-identification
% @variant source-node-fields
% @lean Newspeak.UnidentifiedSourceNode
% @mode unidentified_source_node_fields(+,-,-,-)
unidentified_source_node_fields(
    unidentified_source_node(Key, Sort, Span), Key, Sort, Span).

% @latex equation:stable-ast-identification
% @variant fresh-identity
% @lean Newspeak.freshSourceNodeId
% @mode fresh_source_node_id(+,+,+,+,-)
fresh_source_node_id(
    fresh_source_node_id(FreshProof), Supply, Position, Sort, Identity).

% @latex equation:stable-ast-identification
% @variant retained-identity
% @lean Newspeak.selectedSourceNodeId
% @mode selected_source_node_id(+,+,+,+,+,-)
selected_source_node_id(
    selected_retained, Retained, _Supply, _Position, Node,
    Identity) :-
    unidentified_source_node_fields(Node, Key, _Sort, _Span),
    store_lookup(Retained, Key, some(Identity)).

% @latex equation:stable-ast-identification
% @variant fresh-identity
% @lean Newspeak.selectedSourceNodeId
% @mode selected_source_node_id(+,+,+,+,+,-)
selected_source_node_id(
    selected_fresh(FreshProof), Retained, Supply, Position, Node,
    Identity) :-
    unidentified_source_node_fields(Node, Key, Sort, _Span),
    store_lookup(Retained, Key, none),
    fresh_source_node_id(FreshProof, Supply, Position, Sort, Identity).

% @latex equation:stable-ast-identification
% @variant nodes-empty
% @lean Newspeak.identifySourceNodesFrom
% @mode identify_source_nodes_from(+,+,+,+,+,-)
identify_source_nodes_from(
    identify_nodes_empty, _Retained, _Supply, _Position, [], []).

% @latex equation:stable-ast-identification
% @variant nodes-cons
% @lean Newspeak.identifySourceNodesFrom
% @mode identify_source_nodes_from(+,+,+,+,+,-)
identify_source_nodes_from(
    identify_nodes_cons(SelectionProof, SuccessorProof, RemainingProof),
    Retained, Supply, Position, [Node|Remaining],
    [identified_source_node(Key, Sort, Span, Identity)|IdentifiedRemaining]) :-
    unidentified_source_node_fields(Node, Key, Sort, Span),
    selected_source_node_id(
        SelectionProof, Retained, Supply, Position, Node, Identity),
    natural_successor(SuccessorProof, Position, NextPosition),
    identify_source_nodes_from(
        RemainingProof, Retained, Supply, NextPosition,
        Remaining, IdentifiedRemaining).

% @latex equation:stable-ast-identity-validity
% @variant node-list-check
% @lean Newspeak.identifiedSourceNodesOK
% @mode identified_source_node_list_ok(+,+,+)
identified_source_node_list_ok(
    identified_source_node_list_ok(ValidityProof), Nodes, true).

% @latex equation:stable-ast-identification
% @variant retention-empty
% @lean Newspeak.extendIdentityRetention
% @mode extend_identity_retention(+,+,+,-)
extend_identity_retention(
    extend_retention_empty, Retained, [], Retained).

% @latex equation:stable-ast-identification
% @variant retention-cons
% @lean Newspeak.extendIdentityRetention
% @mode extend_identity_retention(+,+,+,-)
extend_identity_retention(
    extend_retention_cons(RemainingProof),
    Retained,
    [identified_source_node(Key, _Sort, _Span, Identity)|Remaining],
    Extended) :-
    store_install(Retained, Key, Identity, Next),
    extend_identity_retention(
        RemainingProof, Next, Remaining, Extended).

% @latex equation:stable-ast-identification
% @variant identified-node-list
% @lean Newspeak.identifySourceNodes
% @mode identify_source_nodes(+,+,+,+,-)
identify_source_nodes(
    identify_source_nodes(FromProof, ValidityProof, ExtensionProof),
    Retained, Supply, Nodes,
    identification_output(Identified, Extended)) :-
    identify_source_nodes_from(
        FromProof, Retained, Supply, 0, Nodes, Identified),
    identified_source_node_list_ok(ValidityProof, Identified, true),
    extend_identity_retention(
        ExtensionProof, Retained, Identified, Extended).

% @latex equation:stable-ast-identification
% @lean Newspeak.identifySurfaceCompilationUnit
% @mode identify_surface_compilation_unit(+,+,+,+,+)
identify_surface_compilation_unit(
    identification_result(EnumerationProof, IdentificationProof),
    Retained, Supply, Unit, Identification) :-
    surface_compilation_unit_nodes(EnumerationProof, Unit, Nodes),
    identify_source_nodes(
        IdentificationProof, Retained, Supply, Nodes, Identification).

% @latex equation:stable-ast-identity-validity
% @lean Newspeak.IdentifiedSourceNodesOK
% @mode identified_source_nodes_ok(+,+)
identified_source_nodes_ok(
    identified_source_nodes_ok(ValidityProof), Identification).

% @latex equation:surface-context-validity
% @variant front-end-gate
% @lean Newspeak.ProgramDerivationServices.surfaceOK
% @mode surface_compilation_unit_valid(+,+,+,+)
surface_compilation_unit_valid(
    surface_compilation_unit_valid(ValidityProof),
    DerivationServices, Unit, Identification).

% @latex equation:derived-program-indexes
% @variant front-end-result
% @lean Newspeak.ProgramDerivationServices.deriveProgram
% @mode derive_annotated_program(+,+,+,+,+,+)
derive_annotated_program(
    derived_program(DerivationProof), DerivationServices, Unit,
    Identification, Program, Expression).

% @latex equation:annotated-core-checker
% @lean Newspeak.annotatedCoreValidCheck
% @mode annotated_core_check(+,+,+,+,+)
annotated_core_check(
    annotated_core_check(CheckProof), Program, Expression, Fuel, true).

% @latex equation:annotated-core-validity
% @lean Newspeak.AnnotatedCoreValid
% @mode annotated_core_valid(+,+,+,+)
annotated_core_valid(
    annotated_core_valid(ValidityProof), Program, Expression, Fuel).

% @latex equation:source-to-annotated-core
% @variant complete-front-end
% @lean Newspeak.FrontEndDerivation.accepted
% @mode front_end_derivation(+,+,+,+,+,+,+,-)
front_end_derivation(
    front_end_derivation(
        ParseProof, IdentificationProof, SurfaceValidityProof,
        ProgramDerivationProof, CoreValidityProof),
    Grammar, Decoders, DerivationServices, Retained, Supply, Source,
    front_end_result(Program, Expression, NewRetention)) :-
    peg_parses_newspeak_unit(
        ParseProof, Grammar, Decoders, Source, Unit, Metadata),
    identify_surface_compilation_unit(
        IdentificationProof, Retained, Supply, Unit, Identification),
    identification_retention(Identification, NewRetention),
    surface_compilation_unit_valid(
        SurfaceValidityProof, DerivationServices, Unit, Identification),
    derive_annotated_program(
        ProgramDerivationProof, DerivationServices, Unit, Identification,
        Program, Expression),
    derivation_core_fuel(DerivationServices, Fuel),
    annotated_core_valid(
        CoreValidityProof, Program, Expression, Fuel).

% @latex equation:stable-ast-identification
% @variant retention-projection
% @lean Newspeak.IdentificationOutput.retention
% @mode identification_retention(+,-)
identification_retention(
    identification_output(_Nodes, Retention), Retention).

% @latex equation:annotated-core-validity
% @variant fuel-projection
% @lean Newspeak.ProgramDerivationServices.coreFuel
% @mode derivation_core_fuel(+,-)
derivation_core_fuel(
    program_derivation_services(_DeriveProgram, _SurfaceOK, Fuel), Fuel).

% --------------------------------------------------------------------------
% Recursive static elaboration
% --------------------------------------------------------------------------

% The graph premises below expose the environment and retained-identity
% queries used by the recursive equations.  They are separate predicates so
% the elaboration clauses remain readable and no service is hidden in Prolog
% unification.

% @latex equation:static-binding-function
% @lean Newspeak.ElaborationContext.bind
% @mode elaboration_context_bind(+,+,+,+)
elaboration_context_bind(
    context_bind(BindingProof), Context, Name, Binding).

% @latex equation:elaboration-context
% @variant immediate-class
% @lean Newspeak.ElaborationContext.immediateClass
% @mode elaboration_context_immediate_class(+,-)
elaboration_context_immediate_class(
    elaboration_context(
        _EnclosingClassBody, _EnclosingActivation, _ActivationKind,
        ImmediateClass, _Binders, _LocalReturn, _NonlocalReturn),
    ImmediateClass).

% @latex equation:implicit-binding-annotation
% @lean Newspeak.selectorBindingAnnotation
% @mode selector_binding_annotation(+,+,+,+,+)
selector_binding_annotation(
    selector_binding_annotation(AnnotationProof),
    Services, Context, Selector, Annotation).

% @latex equation:elaboration-helper-functions
% @variant retained-identity-query
% @lean Newspeak.ElaborationIdentities
% @mode elaboration_identity(+,+,+,-)
elaboration_identity(
    elaboration_identity(IdentityProof), Services, Query, Result).

% @latex equation:surface-receiver-kind
% @lean Newspeak.surfaceReceiverKind
% @mode surface_receiver_kind(+,+,+,+)
surface_receiver_kind(
    receiver_kind(KindProof), Context, Receiver, Kind).

% @latex equation:front-end-default-superclass
% @lean Newspeak.ElaborationServices.defaultSuperclass
% @mode default_superclass_application(+,+,+,+)
default_superclass_application(
    default_superclass(DefaultProof), Services, Context, Superclass).

% @latex equation:expression-elaboration
% @variant atom
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_atom(SuccessorProof), _Services, _Context, FuelPlusOne,
    surface_atom(_Span, Payload), atom(Payload)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne).

% @latex equation:expression-elaboration
% @variant identifier
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_identifier(SuccessorProof, BindingProof),
    _Services, Context, FuelPlusOne, surface_identifier(_Span, Name),
    implicit_send(selector(Name), [], Binding, Immediate)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    elaboration_context_bind(BindingProof, Context, Name, Binding),
    elaboration_context_immediate_class(Context, Immediate).

% @latex equation:expression-elaboration
% @variant self
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_self(SuccessorProof), _Services, _Context, FuelPlusOne,
    surface_self(_Span), self_value) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne).

% `surface_outer` and `surface_super` deliberately have no successful direct
% clause: they elaborate only as receivers through make_elaborated_send.

% @latex equation:expression-elaboration
% @variant parenthesized
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_parenthesized(SuccessorProof, NestedProof),
    Services, Context, FuelPlusOne,
    surface_parenthesized(_Span, Nested), Core) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        NestedProof, Services, Context, Fuel, Nested, Core).

% @latex equation:expression-elaboration
% @variant implicit-send
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_implicit_send(
        SuccessorProof, ArgumentsProof, AnnotationProof),
    Services, Context, FuelPlusOne,
    surface_implicit_send(_Span, Selector, Arguments),
    implicit_send(Selector, CoreArguments, Annotation, Immediate)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_list_with_fuel(
        ArgumentsProof, Services, Context, Fuel, Arguments, CoreArguments),
    selector_binding_annotation(
        AnnotationProof, Services, Context, Selector, Annotation),
    elaboration_context_immediate_class(Context, Immediate).

% @latex equation:expression-elaboration
% @variant message-send
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_message_send(SuccessorProof, ArgumentsProof, SendProof),
    Services, Context, FuelPlusOne,
    surface_message_send(_Span, Receiver, Selector, Arguments), Core) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_list_with_fuel(
        ArgumentsProof, Services, Context, Fuel, Arguments, CoreArguments),
    make_elaborated_send_with_fuel(
        SendProof, Services, Context, Fuel,
        Receiver, Selector, CoreArguments, Core).

% @latex equation:expression-elaboration
% @variant eventual-send
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_eventual_send(
        SuccessorProof, ReceiverProof, ArgumentsProof),
    Services, Context, FuelPlusOne,
    surface_eventual_send(_Span, Receiver, Selector, Arguments),
    eventual_send(CoreReceiver, Selector, CoreArguments)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        ReceiverProof, Services, Context, Fuel, Receiver, CoreReceiver),
    elaborate_expression_list_with_fuel(
        ArgumentsProof, Services, Context, Fuel, Arguments, CoreArguments).

% @latex equation:cascade-expansion
% @variant surface-elaboration
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_cascade(
        SuccessorProof, IdentityProof, ReceiverProof,
        InitialProof, SubsequentProof),
    Services, Context, FuelPlusOne,
    surface_cascade(Span, Receiver, Initial, Subsequent),
    cascade(Descriptor, CoreReceiver, Clauses)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaboration_context_immediate_class(Context, Immediate),
    elaboration_identity(
        IdentityProof, Services,
        cascade_descriptor(Span, Immediate), some(Descriptor)),
    elaborate_expression_with_fuel(
        ReceiverProof, Services, Context, Fuel, Receiver, CoreReceiver),
    elaborate_clause_list_with_fuel(
        InitialProof, Services, Context, Fuel, Initial, CoreInitial),
    elaborate_clause_list_with_fuel(
        SubsequentProof, Services, Context, Fuel,
        Subsequent, CoreSubsequent),
    list_append(CoreInitial, CoreSubsequent, Clauses).

% @latex equation:setter-expansion
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_setter(SuccessorProof, IdentityProof, ArgumentProof),
    Services, Context, FuelPlusOne,
    surface_setter(Span, _Name, Expression),
    ordinary_send(
        closure_literal(ClosureDeclaration), selector('value:'),
        [Argument])) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaboration_context_immediate_class(Context, Immediate),
    elaboration_identity(
        IdentityProof, Services,
        cascade_descriptor(Span, Immediate),
        some(cascade_descriptor(
            ClosureDeclaration, _ReceiverParameter,
            _ReceiverSelector, _DescriptorImmediateClass))),
    elaborate_expression_with_fuel(
        ArgumentProof, Services, Context, Fuel, Expression, Argument).

% @latex equation:compound-expression-elaboration
% @variant tuple
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_tuple(SuccessorProof, IdentityProof, ElementsProof),
    Services, Context, FuelPlusOne, surface_tuple(Span, Elements),
    tuple(Site, Descriptor, CoreElements)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaboration_context_immediate_class(Context, Immediate),
    elaboration_identity(
        IdentityProof, Services, tuple_descriptor(Span, Immediate),
        some(pair(Site, Descriptor))),
    elaborate_expression_list_with_fuel(
        ElementsProof, Services, Context, Fuel, Elements, CoreElements).

% @latex equation:pattern-elaboration
% @variant expression
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_pattern_expression(
        SuccessorProof, PatternProof, BindingProof),
    Services, Context, FuelPlusOne, surface_pattern(_Span, Pattern),
    pattern(CorePattern, Annotation, Immediate)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_pattern_with_fuel(
        PatternProof, Services, Context, Fuel, Pattern, CorePattern),
    elaboration_context_bind(
        BindingProof, Context, 'Pattern', Annotation),
    elaboration_context_immediate_class(Context, Immediate).

% @latex equation:expression-elaboration
% @variant closure
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_closure(SuccessorProof, IdentityProof),
    Services, _Context, FuelPlusOne,
    surface_closure(Span, _Parameters, _Locals, _Body),
    closure_literal(Declaration)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    elaboration_identity(
        IdentityProof, Services, closure_declaration(Span),
        some(Declaration)).

% @latex equation:front-end-object-elaboration
% @variant expression
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_object_literal(
        SuccessorProof, IdentityProof, SuperclassProof),
    Services, Context, FuelPlusOne,
    surface_object_literal(Span, Header),
    object_literal(Declaration, Superclass)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaboration_identity(
        IdentityProof, Services, object_literal_declaration(Span),
        some(Declaration)),
    elaborate_object_superclass_with_fuel(
        SuperclassProof, Services, Context, Fuel, Header, Superclass).

% @latex equation:front-end-class-body-elaboration
% @variant expression
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_class_expression(
        SuccessorProof, IdentityProof, SuperclassProof),
    Services, Context, FuelPlusOne,
    surface_class_expression(Span, Declaration),
    class_body(ClassIdentity, Superclass)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaboration_identity(
        IdentityProof, Services, class_declaration(Span),
        some(ClassIdentity)),
    elaborate_class_superclass_with_fuel(
        SuperclassProof, Services, Context, Fuel,
        Declaration, Superclass).

% @latex equation:compound-expression-elaboration
% @variant singleton-sequence
% @lean Newspeak.elaborateExpressionWithFuel
% @mode elaborate_expression_with_fuel(+,+,+,+,+,-)
elaborate_expression_with_fuel(
    elaborate_singleton_sequence(SuccessorProof, NestedProof),
    Services, Context, FuelPlusOne,
    surface_sequence(
        _Span, [surface_expression_statement(_StatementSpan, Nested)]),
    Core) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        NestedProof, Services, Context, Fuel, Nested, Core).

% @latex equation:elaboration-helper-functions
% @variant expression-list-empty
% @lean Newspeak.elaborateExpressionListWithFuel
% @mode elaborate_expression_list_with_fuel(+,+,+,+,+,-)
elaborate_expression_list_with_fuel(
    elaborate_expression_list_empty, _Services, _Context, _Fuel, [], []).

% @latex equation:elaboration-helper-functions
% @variant expression-list-cons
% @lean Newspeak.elaborateExpressionListWithFuel
% @mode elaborate_expression_list_with_fuel(+,+,+,+,+,-)
elaborate_expression_list_with_fuel(
    elaborate_expression_list_cons(
        SuccessorProof, FirstProof, RestProof),
    Services, Context, FuelPlusOne, [Expression|Remaining],
    [CoreExpression|CoreRemaining]) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        FirstProof, Services, Context, Fuel, Expression, CoreExpression),
    elaborate_expression_list_with_fuel(
        RestProof, Services, Context, Fuel, Remaining, CoreRemaining).

% @latex equation:elaborated-send-construction
% @variant self
% @lean Newspeak.makeElaboratedSendWithFuel
% @mode make_elaborated_send_with_fuel(+,+,+,+,+,+,+,-)
make_elaborated_send_with_fuel(
    make_self_send(SuccessorProof, KindProof),
    _Services, Context, FuelPlusOne, Receiver, Selector, Arguments,
    self_send(Selector, Arguments, Immediate)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    surface_receiver_kind(
        KindProof, Context, Receiver, some(self_receiver(Immediate))).

% @latex equation:elaborated-send-construction
% @variant outer
% @lean Newspeak.makeElaboratedSendWithFuel
% @mode make_elaborated_send_with_fuel(+,+,+,+,+,+,+,-)
make_elaborated_send_with_fuel(
    make_outer_send(SuccessorProof, KindProof),
    _Services, Context, FuelPlusOne, Receiver, Selector, Arguments,
    outer_send(Selector, Arguments, Target, Immediate)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    surface_receiver_kind(
        KindProof, Context, Receiver,
        some(outer_receiver(Target, Immediate))).

% @latex equation:elaborated-send-construction
% @variant super
% @lean Newspeak.makeElaboratedSendWithFuel
% @mode make_elaborated_send_with_fuel(+,+,+,+,+,+,+,-)
make_elaborated_send_with_fuel(
    make_super_send(SuccessorProof, KindProof),
    _Services, Context, FuelPlusOne, Receiver, Selector, Arguments,
    super_send(Selector, Arguments)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    surface_receiver_kind(
        KindProof, Context, Receiver, some(super_receiver)).

% @latex equation:elaborated-send-construction
% @variant ordinary
% @lean Newspeak.makeElaboratedSendWithFuel
% @mode make_elaborated_send_with_fuel(+,+,+,+,+,+,+,-)
make_elaborated_send_with_fuel(
    make_ordinary_send(SuccessorProof, KindProof, ReceiverProof),
    Services, Context, FuelPlusOne, Receiver, Selector, Arguments,
    ordinary_send(CoreReceiver, Selector, Arguments)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    surface_receiver_kind(
        KindProof, Context, Receiver, some(ordinary_receiver)),
    elaborate_expression_with_fuel(
        ReceiverProof, Services, Context, Fuel, Receiver, CoreReceiver).

% @latex equation:elaboration-helper-functions
% @variant clause-list-empty
% @lean Newspeak.elaborateClauseListWithFuel
% @mode elaborate_clause_list_with_fuel(+,+,+,+,+,-)
elaborate_clause_list_with_fuel(
    elaborate_clause_list_empty, _Services, _Context, _Fuel, [], []).

% @latex equation:elaboration-helper-functions
% @variant clause-list-cons
% @lean Newspeak.elaborateClauseListWithFuel
% @mode elaborate_clause_list_with_fuel(+,+,+,+,+,-)
elaborate_clause_list_with_fuel(
    elaborate_clause_list_cons(
        SuccessorProof, ArgumentsProof, RemainingProof),
    Services, Context, FuelPlusOne,
    [surface_clause(_Span, Selector, Arguments)|Remaining],
    [pair(Selector, CoreArguments)|CoreRemaining]) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_list_with_fuel(
        ArgumentsProof, Services, Context, Fuel, Arguments, CoreArguments),
    elaborate_clause_list_with_fuel(
        RemainingProof, Services, Context, Fuel,
        Remaining, CoreRemaining).

% @latex equation:pattern-elaboration
% @variant wildcard
% @lean Newspeak.elaboratePatternWithFuel
% @mode elaborate_pattern_with_fuel(+,+,+,+,+,-)
elaborate_pattern_with_fuel(
    elaborate_wildcard_pattern(SuccessorProof),
    _Services, _Context, FuelPlusOne,
    surface_wildcard_pattern(_Span), wildcard_pattern) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne).

% @latex equation:pattern-elaboration
% @variant literal
% @lean Newspeak.elaboratePatternWithFuel
% @mode elaborate_pattern_with_fuel(+,+,+,+,+,-)
elaborate_pattern_with_fuel(
    elaborate_literal_pattern(SuccessorProof, ExpressionProof),
    Services, Context, FuelPlusOne,
    surface_literal_pattern(_Span, Expression),
    literal_pattern(CoreExpression)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        ExpressionProof, Services, Context, Fuel,
        Expression, CoreExpression).

% @latex equation:pattern-elaboration
% @variant variable
% @lean Newspeak.elaboratePatternWithFuel
% @mode elaborate_pattern_with_fuel(+,+,+,+,+,-)
elaborate_pattern_with_fuel(
    elaborate_variable_pattern(SuccessorProof, IdentityProof),
    Services, _Context, FuelPlusOne,
    surface_variable_pattern(Span, _Name), variable_pattern(Site)) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    elaboration_identity(
        IdentityProof, Services, variable_pattern_site(Span), some(Site)).

% @latex equation:pattern-elaboration
% @variant nested
% @lean Newspeak.elaboratePatternWithFuel
% @mode elaborate_pattern_with_fuel(+,+,+,+,+,-)
elaborate_pattern_with_fuel(
    elaborate_nested_pattern(SuccessorProof, NestedProof),
    Services, Context, FuelPlusOne,
    surface_nested_pattern(_Span, Nested), nested_pattern(CoreNested)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_pattern_with_fuel(
        NestedProof, Services, Context, Fuel, Nested, CoreNested).

% @latex equation:pattern-elaboration
% @variant keyword
% @lean Newspeak.elaboratePatternWithFuel
% @mode elaborate_pattern_with_fuel(+,+,+,+,+,-)
elaborate_pattern_with_fuel(
    elaborate_keyword_pattern(SuccessorProof, IdentityProof, PairsProof),
    Services, Context, FuelPlusOne,
    surface_keyword_pattern(Span, Pairs),
    keyword_pattern(
        KeywordSite, KeywordDescriptor,
        ComponentSite, ComponentDescriptor, CorePairs)) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaboration_context_immediate_class(Context, Immediate),
    elaboration_identity(
        IdentityProof, Services,
        keyword_pattern_descriptors(Span, Immediate),
        some(keyword_pattern_descriptor_tuple(
            KeywordSite, KeywordDescriptor,
            ComponentSite, ComponentDescriptor))),
    elaborate_pattern_pairs_with_fuel(
        PairsProof, Services, Context, Fuel, Pairs, CorePairs).

% @latex equation:pattern-elaboration
% @variant pairs-empty
% @lean Newspeak.elaboratePatternPairsWithFuel
% @mode elaborate_pattern_pairs_with_fuel(+,+,+,+,+,-)
elaborate_pattern_pairs_with_fuel(
    elaborate_pattern_pairs_empty,
    _Services, _Context, _Fuel, [], []).

% @latex equation:pattern-elaboration
% @variant pair-absent
% @lean Newspeak.elaboratePatternPairsWithFuel
% @mode elaborate_pattern_pairs_with_fuel(+,+,+,+,+,-)
elaborate_pattern_pairs_with_fuel(
    elaborate_pattern_pair_absent(SuccessorProof, RemainingProof),
    Services, Context, FuelPlusOne,
    [pair(Selector, none)|Remaining],
    [pair(Selector, wildcard_pattern)|CoreRemaining]) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_pattern_pairs_with_fuel(
        RemainingProof, Services, Context, Fuel,
        Remaining, CoreRemaining).

% @latex equation:pattern-elaboration
% @variant pair-present
% @lean Newspeak.elaboratePatternPairsWithFuel
% @mode elaborate_pattern_pairs_with_fuel(+,+,+,+,+,-)
elaborate_pattern_pairs_with_fuel(
    elaborate_pattern_pair_present(
        SuccessorProof, PatternProof, RemainingProof),
    Services, Context, FuelPlusOne,
    [pair(Selector, some(Pattern))|Remaining],
    [pair(Selector, CorePattern)|CoreRemaining]) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_pattern_with_fuel(
        PatternProof, Services, Context, Fuel, Pattern, CorePattern),
    elaborate_pattern_pairs_with_fuel(
        RemainingProof, Services, Context, Fuel,
        Remaining, CoreRemaining).

% @latex equation:front-end-default-superclass
% @variant object-implicit
% @lean Newspeak.elaborateObjectSuperclassWithFuel
% @mode elaborate_object_superclass_with_fuel(+,+,+,+,+,-)
elaborate_object_superclass_with_fuel(
    elaborate_object_implicit_superclass(SuccessorProof, DefaultProof),
    Services, Context, FuelPlusOne,
    surface_implicit_header(_Span, _Structure), Superclass) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    default_superclass_application(
        DefaultProof, Services, Context, Superclass).

% @latex equation:front-end-default-superclass
% @variant object-explicit
% @lean Newspeak.elaborateObjectSuperclassWithFuel
% @mode elaborate_object_superclass_with_fuel(+,+,+,+,+,-)
elaborate_object_superclass_with_fuel(
    elaborate_object_explicit_superclass(SuccessorProof, ReceiverProof),
    Services, Context, FuelPlusOne,
    surface_explicit_header(
        _Span, Receiver, _Initializer, _Structure), Superclass) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        ReceiverProof, Services, Context, Fuel, Receiver, Superclass).

% @latex equation:front-end-default-superclass
% @variant class-default
% @lean Newspeak.elaborateClassSuperclassWithFuel
% @mode elaborate_class_superclass_with_fuel(+,+,+,+,+,-)
elaborate_class_superclass_with_fuel(
    elaborate_class_default_superclass(SuccessorProof, DefaultProof),
    Services, Context, FuelPlusOne,
    surface_class_declaration(
        _Span, _Name, _FactorySelector, _FactoryFormals,
        surface_default_inheritance(_InheritanceSpan, _Structure)),
    Superclass) :-
    natural_successor(SuccessorProof, _Fuel, FuelPlusOne),
    default_superclass_application(
        DefaultProof, Services, Context, Superclass).

% @latex equation:front-end-default-superclass
% @variant class-explicit
% @lean Newspeak.elaborateClassSuperclassWithFuel
% @mode elaborate_class_superclass_with_fuel(+,+,+,+,+,-)
elaborate_class_superclass_with_fuel(
    elaborate_class_explicit_superclass(SuccessorProof, ReceiverProof),
    Services, Context, FuelPlusOne,
    surface_class_declaration(
        _Span, _Name, _FactorySelector, _FactoryFormals,
        surface_explicit_inheritance(
            _InheritanceSpan, Receiver, _Initializer, _Structure)),
    Superclass) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        ReceiverProof, Services, Context, Fuel, Receiver, Superclass).

% @latex equation:front-end-default-superclass
% @variant class-mixin-chain
% @lean Newspeak.elaborateClassSuperclassWithFuel
% @mode elaborate_class_superclass_with_fuel(+,+,+,+,+,-)
elaborate_class_superclass_with_fuel(
    elaborate_class_mixin_superclass(SuccessorProof, ReceiverProof),
    Services, Context, FuelPlusOne,
    surface_class_declaration(
        _Span, _Name, _FactorySelector, _FactoryFormals,
        surface_mixin_chain(
            _InheritanceSpan, Receiver, _Initializer,
            _Additional, _Structure)),
    Superclass) :-
    natural_successor(SuccessorProof, Fuel, FuelPlusOne),
    elaborate_expression_with_fuel(
        ReceiverProof, Services, Context, Fuel, Receiver, Superclass).

% --------------------------------------------------------------------------
% Statements and local declarations
% --------------------------------------------------------------------------

% @latex equation:elaboration-function-signatures
% @variant service-fuel
% @lean Newspeak.ElaborationServices.fuel
% @mode elaboration_services_fuel(+,+,-)
elaboration_services_fuel(
    elaboration_services_fuel(FuelProof), Services, Fuel).

% @latex equation:expression-elaboration
% @variant configured-fuel
% @lean Newspeak.elaborateExpression
% @mode elaborate_expression(+,+,+,+,-)
elaborate_expression(
    elaborate_expression(FuelProof, ExpressionProof),
    Services, Context, Surface, Core) :-
    elaboration_services_fuel(FuelProof, Services, Fuel),
    elaborate_expression_with_fuel(
        ExpressionProof, Services, Context, Fuel, Surface, Core).

% @latex equation:compound-expression-elaboration
% @variant return-permitted-local
% @lean Newspeak.ElaborationContext.localReturnPermitted
% @mode elaboration_return_permitted(+,+)
elaboration_return_permitted(
    return_permitted_local,
    elaboration_context(
        _ClassBody, _Activation, _Kind, _Immediate, _Binders,
        true, _NonlocalReturn)).

% @latex equation:compound-expression-elaboration
% @variant return-permitted-nonlocal
% @lean Newspeak.ElaborationContext.nonlocalReturnPermitted
% @mode elaboration_return_permitted(+,+)
elaboration_return_permitted(
    return_permitted_nonlocal,
    elaboration_context(
        _ClassBody, _Activation, _Kind, _Immediate, _Binders,
        false, true)).

% @latex equation:compound-expression-elaboration
% @variant expression-statement
% @lean Newspeak.elaborateStatement
% @mode elaborate_statement(+,+,+,+,-)
elaborate_statement(
    elaborate_expression_statement(ExpressionProof),
    Services, Context,
    surface_expression_statement(_Span, Surface),
    expression_statement(Core)) :-
    elaborate_expression(
        ExpressionProof, Services, Context, Surface, Core).

% @latex equation:compound-expression-elaboration
% @variant return-statement
% @lean Newspeak.elaborateStatement
% @mode elaborate_statement(+,+,+,+,-)
elaborate_statement(
    elaborate_return_statement(ReturnProof, ExpressionProof),
    Services, Context,
    surface_return_statement(_Span, Surface),
    return_statement(Core)) :-
    elaboration_return_permitted(ReturnProof, Context),
    elaborate_expression(
        ExpressionProof, Services, Context, Surface, Core).

% @latex equation:compound-expression-elaboration
% @variant statements-empty
% @lean Newspeak.elaborateStatements
% @mode elaborate_statements(+,+,+,+,-)
elaborate_statements(
    elaborate_statements_empty, _Services, _Context, [], []).

% @latex equation:compound-expression-elaboration
% @variant statements-cons
% @lean Newspeak.elaborateStatements
% @mode elaborate_statements(+,+,+,+,-)
elaborate_statements(
    elaborate_statements_cons(StatementProof, RemainingProof),
    Services, Context, [Statement|Remaining], [Core|CoreRemaining]) :-
    elaborate_statement(
        StatementProof, Services, Context, Statement, Core),
    elaborate_statements(
        RemainingProof, Services, Context, Remaining, CoreRemaining).

% @latex equation:stable-ast-identification
% @variant declaration-identity-query
% @lean Newspeak.declarationIdAt
% @mode declaration_identity_at(+,+,+,+,-)
declaration_identity_at(
    declaration_identity_at(IdentityProof),
    Identification, Span, Kind, Identity).

% @latex equation:local-group-elaboration
% @variant local-identity-injection
% @lean Newspeak.declarationLocalIdentity
% @mode declaration_local_identity(+,+,-)
declaration_local_identity(
    declaration_local_identity(IdentityProof), Declaration, LocalSlot).

% @latex equation:local-group-elaboration
% @variant ordinary-local-identity
% @lean Newspeak.localDeclarationId
% @mode local_declaration_id(+,+,+,-,-)
local_declaration_id(
    local_ordinary_identity(IdentityProof), Identification,
    surface_slot(Span, _Access, Name, _Mutability, _Initializer),
    Declaration, Name) :-
    declaration_identity_at(
        IdentityProof, Identification, Span, slot, Declaration).

% @latex equation:local-group-elaboration
% @variant lazy-local-identity
% @lean Newspeak.localDeclarationId
% @mode local_declaration_id(+,+,+,-,-)
local_declaration_id(
    local_lazy_identity(IdentityProof), Identification,
    surface_lazy_slot(Span, _Access, Name, _Mutability, _Initializer),
    Declaration, Name) :-
    declaration_identity_at(
        IdentityProof, Identification, Span, lazy_slot, Declaration).

% @latex equation:local-group-elaboration
% @variant immutable-initialized
% @lean Newspeak.elaborateLocalDeclaration
% @mode elaborate_local_declaration(+,+,+,+,+,-)
elaborate_local_declaration(
    elaborate_immutable_local(IdentityProof, SlotProof, ExpressionProof),
    Identification, Services, Context,
    surface_slot(Span, Access, Name, immutable, some(Expression)),
    immutable_local(LocalSlot, Core)) :-
    local_declaration_id(
        IdentityProof, Identification,
        surface_slot(Span, Access, Name, immutable, some(Expression)),
        Declaration, Name),
    declaration_local_identity(SlotProof, Declaration, LocalSlot),
    elaborate_expression(
        ExpressionProof, Services, Context, Expression, Core).

% @latex equation:local-group-elaboration
% @variant mutable-initialized
% @lean Newspeak.elaborateLocalDeclaration
% @mode elaborate_local_declaration(+,+,+,+,+,-)
elaborate_local_declaration(
    elaborate_mutable_local(IdentityProof, SlotProof, ExpressionProof),
    Identification, Services, Context,
    surface_slot(Span, Access, Name, mutable, some(Expression)),
    mutable_initialized_local(LocalSlot, Core)) :-
    local_declaration_id(
        IdentityProof, Identification,
        surface_slot(Span, Access, Name, mutable, some(Expression)),
        Declaration, Name),
    declaration_local_identity(SlotProof, Declaration, LocalSlot),
    elaborate_expression(
        ExpressionProof, Services, Context, Expression, Core).

% @latex equation:local-group-elaboration
% @variant mutable-uninitialized
% @lean Newspeak.elaborateLocalDeclaration
% @mode elaborate_local_declaration(+,+,+,+,+,-)
elaborate_local_declaration(
    elaborate_uninitialized_local(IdentityProof, SlotProof),
    Identification, _Services, _Context,
    surface_slot(Span, Access, Name, mutable, none),
    mutable_uninitialized_local(LocalSlot)) :-
    local_declaration_id(
        IdentityProof, Identification,
        surface_slot(Span, Access, Name, mutable, none),
        Declaration, Name),
    declaration_local_identity(SlotProof, Declaration, LocalSlot).

% @latex equation:local-group-elaboration
% @variant lazy-immutable
% @lean Newspeak.elaborateLocalDeclaration
% @mode elaborate_local_declaration(+,+,+,+,+,-)
elaborate_local_declaration(
    elaborate_lazy_immutable_local(
        IdentityProof, SlotProof, ExpressionProof),
    Identification, Services, Context,
    surface_lazy_slot(Span, Access, Name, immutable, Expression),
    lazy_immutable_local(LocalSlot, Core)) :-
    local_declaration_id(
        IdentityProof, Identification,
        surface_lazy_slot(Span, Access, Name, immutable, Expression),
        Declaration, Name),
    declaration_local_identity(SlotProof, Declaration, LocalSlot),
    elaborate_expression(
        ExpressionProof, Services, Context, Expression, Core).

% @latex equation:local-group-elaboration
% @variant lazy-mutable
% @lean Newspeak.elaborateLocalDeclaration
% @mode elaborate_local_declaration(+,+,+,+,+,-)
elaborate_local_declaration(
    elaborate_lazy_mutable_local(
        IdentityProof, SlotProof, ExpressionProof),
    Identification, Services, Context,
    surface_lazy_slot(Span, Access, Name, mutable, Expression),
    lazy_mutable_local(LocalSlot, Core)) :-
    local_declaration_id(
        IdentityProof, Identification,
        surface_lazy_slot(Span, Access, Name, mutable, Expression),
        Declaration, Name),
    declaration_local_identity(SlotProof, Declaration, LocalSlot),
    elaborate_expression(
        ExpressionProof, Services, Context, Expression, Core).

% @latex equation:local-group-elaboration
% @variant declaration-list-empty
% @lean Newspeak.elaborateLocalDeclarationList
% @mode elaborate_local_declaration_list(+,+,+,+,+,-)
elaborate_local_declaration_list(
    elaborate_local_declarations_empty,
    _Identification, _Services, _Context, [], []).

% @latex equation:local-group-elaboration
% @variant declaration-list-cons
% @lean Newspeak.elaborateLocalDeclarationList
% @mode elaborate_local_declaration_list(+,+,+,+,+,-)
elaborate_local_declaration_list(
    elaborate_local_declarations_cons(DeclarationProof, RemainingProof),
    Identification, Services, Context,
    [Declaration|Remaining], [Local|LocalRemaining]) :-
    elaborate_local_declaration(
        DeclarationProof, Identification, Services, Context,
        Declaration, Local),
    elaborate_local_declaration_list(
        RemainingProof, Identification, Services, Context,
        Remaining, LocalRemaining).

% @latex equation:local-group-elaboration
% @variant sequential-wrapping-empty
% @lean Newspeak.LocalDeclarationGroup.sequential
% @mode wrap_sequential_locals(+,-)
wrap_sequential_locals([], []).

% @latex equation:local-group-elaboration
% @variant sequential-wrapping-cons
% @lean Newspeak.LocalDeclarationGroup.sequential
% @mode wrap_sequential_locals(+,-)
wrap_sequential_locals(
    [Local|Remaining],
    [sequential_local(Local)|WrappedRemaining]) :-
    wrap_sequential_locals(Remaining, WrappedRemaining).

% @latex equation:local-group-elaboration
% @variant groups-empty
% @lean Newspeak.elaborateLocalGroups
% @mode elaborate_local_groups(+,+,+,+,+,-)
elaborate_local_groups(
    elaborate_local_groups_empty,
    _Identification, _Services, _Context, [], []).

% @latex equation:local-group-elaboration
% @variant sequential-group
% @lean Newspeak.elaborateLocalGroups
% @mode elaborate_local_groups(+,+,+,+,+,-)
elaborate_local_groups(
    elaborate_sequential_local_group(
        DeclarationsProof, RemainingProof),
    Identification, Services, Context,
    [surface_sequential_group(_Span, Declarations)|Remaining], Groups) :-
    elaborate_local_declaration_list(
        DeclarationsProof, Identification, Services, Context,
        Declarations, Locals),
    wrap_sequential_locals(Locals, SequentialGroups),
    elaborate_local_groups(
        RemainingProof, Identification, Services, Context,
        Remaining, RemainingGroups),
    list_append(SequentialGroups, RemainingGroups, Groups).

% @latex equation:local-group-elaboration
% @variant simultaneous-group
% @lean Newspeak.elaborateLocalGroups
% @mode elaborate_local_groups(+,+,+,+,+,-)
elaborate_local_groups(
    elaborate_simultaneous_local_group(
        DeclarationsProof, RemainingProof),
    Identification, Services, Context,
    [surface_simultaneous_group(_Span, Declarations)|Remaining],
    [simultaneous_locals(Locals)|RemainingGroups]) :-
    elaborate_local_declaration_list(
        DeclarationsProof, Identification, Services, Context,
        Declarations, Locals),
    elaborate_local_groups(
        RemainingProof, Identification, Services, Context,
        Remaining, RemainingGroups).

% @latex equation:declaration-elaboration
% @variant parameter-identity-injection
% @lean Newspeak.declarationParameterIdentity
% @mode declaration_parameter_identity(+,+,-)
declaration_parameter_identity(
    declaration_parameter_identity(IdentityProof),
    Declaration, Parameter).

% @latex equation:declaration-elaboration
% @variant formal-parameter
% @lean Newspeak.formalParameterId
% @mode formal_parameter_id(+,+,+,-)
formal_parameter_id(
    formal_parameter_id(DeclarationProof, ParameterProof),
    Identification, surface_formal(Span, _Name), Parameter) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, formal, Declaration),
    declaration_parameter_identity(
        ParameterProof, Declaration, Parameter).

% @latex equation:declaration-elaboration
% @variant formal-parameters-empty
% @lean Newspeak.formalParameterIds
% @mode formal_parameter_ids(+,+,+,-)
formal_parameter_ids(
    formal_parameter_ids_empty, _Identification, [], []).

% @latex equation:declaration-elaboration
% @variant formal-parameters-cons
% @lean Newspeak.formalParameterIds
% @mode formal_parameter_ids(+,+,+,-)
formal_parameter_ids(
    formal_parameter_ids_cons(ParameterProof, RemainingProof),
    Identification, [Formal|Remaining], [Parameter|Parameters]) :-
    formal_parameter_id(
        ParameterProof, Identification, Formal, Parameter),
    formal_parameter_ids(
        RemainingProof, Identification, Remaining, Parameters).

% @latex equation:derived-mixin-entry
% @variant slot-identity-injection
% @lean Newspeak.declarationSlotIdentity
% @mode declaration_slot_identity(+,+,-)
declaration_slot_identity(
    declaration_slot_identity(IdentityProof), Declaration, Slot).

% @latex equation:declaration-elaboration
% @variant initializer-thunk-identity
% @lean Newspeak.synthesizedActivationIdentity
% @mode synthesized_activation_identity(+,+,+,-)
synthesized_activation_identity(
    synthesized_activation_identity(IdentityProof),
    Declaration, Index, Activation).

% @latex equation:derived-mixin-entry
% @variant physical-slots-empty
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(physical_slots_empty, _Identification, [], []).

% @latex equation:derived-mixin-entry
% @variant physical-slot
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(
    physical_slot(
        DeclarationProof, SlotProof, RemainingProof),
    Identification,
    [surface_slot(Span, _Access, _Name, _Mutability, _Initializer)|Remaining],
    [Slot|Slots]) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, slot, Declaration),
    declaration_slot_identity(SlotProof, Declaration, Slot),
    physical_slot_ids(RemainingProof, Identification, Remaining, Slots).

% @latex equation:derived-mixin-entry
% @variant physical-lazy-slot
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(
    physical_lazy_slot(
        DeclarationProof, SlotProof, RemainingProof),
    Identification,
    [surface_lazy_slot(
        Span, _Access, _Name, _Mutability, _Initializer)|Remaining],
    [Slot|Slots]) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, lazy_slot, Declaration),
    declaration_slot_identity(SlotProof, Declaration, Slot),
    physical_slot_ids(RemainingProof, Identification, Remaining, Slots).

% @latex equation:derived-mixin-entry
% @variant physical-skip-formal
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(
    physical_skip_formal(RemainingProof), Identification,
    [surface_formal(_Span, _Name)|Remaining], Slots) :-
    physical_slot_ids(RemainingProof, Identification, Remaining, Slots).

% @latex equation:derived-mixin-entry
% @variant physical-skip-method
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(
    physical_skip_method(RemainingProof), Identification,
    [surface_method(
        _Span, _Access, _Selector, _Formals, _Locals, _Body)|Remaining],
    Slots) :-
    physical_slot_ids(RemainingProof, Identification, Remaining, Slots).

% @latex equation:derived-mixin-entry
% @variant physical-skip-nested-class
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(
    physical_skip_nested_class(RemainingProof), Identification,
    [surface_nested_class(_Span, _Access, _Declaration)|Remaining], Slots) :-
    physical_slot_ids(RemainingProof, Identification, Remaining, Slots).

% @latex equation:derived-mixin-entry
% @variant physical-skip-class
% @lean Newspeak.physicalSlotIds
% @mode physical_slot_ids(+,+,+,-)
physical_slot_ids(
    physical_skip_class(RemainingProof), Identification,
    [surface_class_declaration(
        _Span, _Name, _Selector, _Formals, _Inheritance)|Remaining], Slots) :-
    physical_slot_ids(RemainingProof, Identification, Remaining, Slots).

% @latex equation:declaration-elaboration
% @variant eager-immutable-slot
% @lean Newspeak.elaborateEagerSlotDeclaration
% @mode elaborate_eager_slot_declaration(+,+,+,+,+,-)
elaborate_eager_slot_declaration(
    eager_immutable_slot(
        DeclarationProof, SlotProof, ThunkProof, ExpressionProof),
    Identification, Services, Context,
    surface_slot(Span, _Access, _Name, immutable, some(Expression)),
    some(immutable_slot(Slot, Core, Thunk))) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, slot, Declaration),
    declaration_slot_identity(SlotProof, Declaration, Slot),
    synthesized_activation_identity(ThunkProof, Declaration, 2, Thunk),
    elaborate_expression(
        ExpressionProof, Services, Context, Expression, Core).

% @latex equation:declaration-elaboration
% @variant eager-mutable-initialized-slot
% @lean Newspeak.elaborateEagerSlotDeclaration
% @mode elaborate_eager_slot_declaration(+,+,+,+,+,-)
elaborate_eager_slot_declaration(
    eager_mutable_initialized_slot(
        DeclarationProof, SlotProof, ThunkProof, ExpressionProof),
    Identification, Services, Context,
    surface_slot(Span, _Access, _Name, mutable, some(Expression)),
    some(mutable_initialized_slot(Slot, Core, Thunk))) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, slot, Declaration),
    declaration_slot_identity(SlotProof, Declaration, Slot),
    synthesized_activation_identity(ThunkProof, Declaration, 2, Thunk),
    elaborate_expression(
        ExpressionProof, Services, Context, Expression, Core).

% @latex equation:declaration-elaboration
% @variant eager-mutable-uninitialized-slot
% @lean Newspeak.elaborateEagerSlotDeclaration
% @mode elaborate_eager_slot_declaration(+,+,+,+,+,-)
elaborate_eager_slot_declaration(
    eager_mutable_uninitialized_slot(DeclarationProof, SlotProof),
    Identification, _Services, _Context,
    surface_slot(Span, _Access, _Name, mutable, none),
    some(mutable_uninitialized_slot(Slot))) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, slot, Declaration),
    declaration_slot_identity(SlotProof, Declaration, Slot).

% @latex equation:declaration-elaboration
% @variant eager-lazy-slot-omitted
% @lean Newspeak.elaborateEagerSlotDeclaration
% @mode elaborate_eager_slot_declaration(+,+,+,+,+,-)
elaborate_eager_slot_declaration(
    eager_lazy_slot_omitted, _Identification, _Services, _Context,
    surface_lazy_slot(
        _Span, _Access, _Name, _Mutability, _Initializer), none).

% @latex equation:declaration-elaboration
% @variant eager-slots-empty
% @lean Newspeak.elaborateEagerSlotDeclarations
% @mode elaborate_eager_slot_declarations(+,+,+,+,+,-)
elaborate_eager_slot_declarations(
    eager_slots_empty, _Identification, _Services, _Context, [], []).

% @latex equation:declaration-elaboration
% @variant eager-slots-omitted
% @lean Newspeak.elaborateEagerSlotDeclarations
% @mode elaborate_eager_slot_declarations(+,+,+,+,+,-)
elaborate_eager_slot_declarations(
    eager_slots_omitted(CurrentProof, RemainingProof),
    Identification, Services, Context,
    [Declaration|Remaining], Slots) :-
    elaborate_eager_slot_declaration(
        CurrentProof, Identification, Services, Context, Declaration, none),
    elaborate_eager_slot_declarations(
        RemainingProof, Identification, Services, Context, Remaining, Slots).

% @latex equation:declaration-elaboration
% @variant eager-slots-cons
% @lean Newspeak.elaborateEagerSlotDeclarations
% @mode elaborate_eager_slot_declarations(+,+,+,+,+,-)
elaborate_eager_slot_declarations(
    eager_slots_cons(CurrentProof, RemainingProof),
    Identification, Services, Context,
    [Declaration|Remaining], [Slot|Slots]) :-
    elaborate_eager_slot_declaration(
        CurrentProof, Identification, Services, Context,
        Declaration, some(Slot)),
    elaborate_eager_slot_declarations(
        RemainingProof, Identification, Services, Context, Remaining, Slots).

% @latex equation:declaration-elaboration
% @variant sequential-initializer-group
% @lean Newspeak.elaborateInitializerGroup
% @mode elaborate_initializer_group(+,+,+,+,+,-)
elaborate_initializer_group(
    sequential_initializer_group(DeclarationsProof),
    Identification, Services, Context,
    surface_sequential_group(_Span, Declarations),
    sequential_slot_group(Slots)) :-
    elaborate_eager_slot_declarations(
        DeclarationsProof, Identification, Services, Context,
        Declarations, Slots).

% @latex equation:declaration-elaboration
% @variant simultaneous-initializer-group
% @lean Newspeak.elaborateInitializerGroup
% @mode elaborate_initializer_group(+,+,+,+,+,-)
elaborate_initializer_group(
    simultaneous_initializer_group(DeclarationsProof),
    Identification, Services, Context,
    surface_simultaneous_group(_Span, Declarations),
    simultaneous_slot_group(Slots)) :-
    elaborate_eager_slot_declarations(
        DeclarationsProof, Identification, Services, Context,
        Declarations, Slots).

% @latex equation:declaration-elaboration
% @variant no-initializer-group
% @lean Newspeak.elaborateInitializerGroups
% @mode elaborate_initializer_groups(+,+,+,+,+,-)
elaborate_initializer_groups(
    no_initializer_group, _Identification, _Services, _Context, none, []).

% @latex equation:declaration-elaboration
% @variant one-initializer-group
% @lean Newspeak.elaborateInitializerGroups
% @mode elaborate_initializer_groups(+,+,+,+,+,-)
elaborate_initializer_groups(
    one_initializer_group(GroupProof),
    Identification, Services, Context, some(Group), [Core]) :-
    elaborate_initializer_group(
        GroupProof, Identification, Services, Context, Group, Core).

% @latex equation:declaration-elaboration
% @variant access-default
% @lean Newspeak.accessOrProtected
% @mode access_or_protected(+,-)
access_or_protected(none, protected_access).

% @latex equation:declaration-elaboration
% @variant access-public
% @lean Newspeak.accessOrProtected
% @mode access_or_protected(+,-)
access_or_protected(some(public_access), public_access).

% @latex equation:declaration-elaboration
% @variant access-protected
% @lean Newspeak.accessOrProtected
% @mode access_or_protected(+,-)
access_or_protected(some(protected_access), protected_access).

% @latex equation:declaration-elaboration
% @variant access-private
% @lean Newspeak.accessOrProtected
% @mode access_or_protected(+,-)
access_or_protected(some(private_access), private_access).

% @latex equation:declaration-elaboration
% @variant ordinary-slot-methods
% @lean Newspeak.ordinarySlotMethods
% @mode ordinary_slot_methods(+,+,+,+,+,+,-)
ordinary_slot_methods(
    ordinary_slot_methods(MethodsProof), Declaration, Owner, Name,
    Access, Mutability, Methods).

% @latex equation:declaration-elaboration
% @variant lazy-slot-methods
% @lean Newspeak.lazySlotMethods
% @mode lazy_slot_methods(+,+,+,+,+,+,+,-)
lazy_slot_methods(
    lazy_slot_methods(MethodsProof), Declaration, Owner, Name,
    Access, Mutability, Initializer, Methods).

% @latex equation:declaration-elaboration
% @variant install-derived-methods
% @lean Newspeak.addDerivedMethods
% @mode add_derived_methods(+,+,+,+,-)
add_derived_methods(
    add_derived_methods(InstallationProof),
    Image, Mixin, Methods, Installed).

% @latex equation:declaration-elaboration
% @variant method-identity
% @lean Newspeak.declarationMethodIdentity
% @mode declaration_method_identity(+,+,-)
declaration_method_identity(
    declaration_method_identity(IdentityProof), Declaration, Method).

% @latex equation:declaration-elaboration
% @variant activation-identity
% @lean Newspeak.declarationActivationIdentity
% @mode declaration_activation_identity(+,+,-)
declaration_activation_identity(
    declaration_activation_identity(IdentityProof), Declaration, Activation).

% @latex equation:local-group-elaboration
% @variant group-declaration-flattening
% @lean Newspeak.surfaceGroupsDeclarations
% @mode surface_groups_declarations(+,+,-)
surface_groups_declarations(
    surface_groups_declarations(FlatteningProof), Groups, Declarations).

% @latex equation:declaration-elaboration
% @variant local-identity-list
% @lean Newspeak.localIdentityList
% @mode local_identity_list(+,+,+,-)
local_identity_list(
    local_identity_list(IdentityProof), Identification, Groups, Locals).

% @latex equation:elaboration-context-extension
% @variant explicit-method-context
% @lean Newspeak.PrologBridge.explicitMethodContext
% @mode explicit_method_context(+,+,+,+,-)
explicit_method_context(
    explicit_method_context(ContextProof), ClassContext, Activation,
    DirectDeclarations, MethodContext).

% @latex equation:declaration-elaboration
% @variant explicit-method-definition
% @lean Newspeak.PrologBridge.explicitMethodDefinition
% @mode explicit_method_definition(+,+,+,+,+,+,+,+,+,-)
explicit_method_definition(
    explicit_method_definition(DefinitionProof), Declaration, Method,
    Activation, Selector, Access, Parameters, Locals, Owner, Definition).

% @latex equation:derived-mixin-entry
% @variant add-method
% @lean Newspeak.DerivedProgramImage.addMethod
% @mode derived_image_add_method(+,+,+,+,+,+,-)
derived_image_add_method(
    derived_image_add_method(InstallationProof), Image, Mixin, Definition,
    LocalGroups, Body, Installed).

% @latex equation:derived-program-indexes
% @variant activation-members
% @lean Newspeak.addActivationMembers
% @mode add_activation_members(+,+,+,+,-)
add_activation_members(
    add_activation_members(InstallationProof), Image, Activation,
    Declarations, Installed).

% @latex equation:declaration-elaboration
% @variant explicit-method
% @lean Newspeak.deriveExplicitMethod
% @mode derive_explicit_method(+,+,+,+,+,+,+,+,-)
derive_explicit_method(
    derive_explicit_method(
        DeclarationProof, MethodProof, ActivationProof, ParametersProof,
        LocalsProof, GroupDeclarationsProof, ContextProof,
        LocalGroupsProof, BodyProof, DefinitionProof,
        MethodInstallationProof, MemberInstallationProof),
    Identification, Services, ClassContext, Owner, Mixin, Image,
    surface_method(Span, AccessOption, Selector, Formals, LocalGroups, Body),
    Complete) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, method, Declaration),
    declaration_method_identity(MethodProof, Declaration, Method),
    declaration_activation_identity(
        ActivationProof, Declaration, Activation),
    formal_parameter_ids(
        ParametersProof, Identification, Formals, Parameters),
    local_identity_list(
        LocalsProof, Identification, LocalGroups, Locals),
    surface_groups_declarations(
        GroupDeclarationsProof, LocalGroups, LocalDeclarations),
    list_append(Formals, LocalDeclarations, DirectDeclarations),
    explicit_method_context(
        ContextProof, ClassContext, Activation,
        DirectDeclarations, MethodContext),
    elaborate_local_groups(
        LocalGroupsProof, Identification, Services, MethodContext,
        LocalGroups, ElaboratedLocals),
    elaborate_statements(
        BodyProof, Services, MethodContext, Body, ElaboratedBody),
    access_or_protected(AccessOption, Access),
    explicit_method_definition(
        DefinitionProof, Declaration, Method, Activation, Selector, Access,
        Parameters, Locals, Owner, Definition),
    derived_image_add_method(
        MethodInstallationProof, Image, Mixin, Definition,
        ElaboratedLocals, ElaboratedBody, Installed),
    add_activation_members(
        MemberInstallationProof, Installed, Activation,
        DirectDeclarations, Complete).

% @latex equation:declaration-elaboration
% @variant member-method
% @lean Newspeak.deriveMemberDeclaration
% @mode derive_member_declaration(+,+,+,+,+,+,+,+,-)
derive_member_declaration(
    derive_member_method(MethodProof),
    Identification, Services, Context, Owner, Mixin, Image,
    surface_method(Span, Access, Selector, Formals, Locals, Body),
    Installed) :-
    derive_explicit_method(
        MethodProof, Identification, Services, Context, Owner, Mixin,
        Image,
        surface_method(Span, Access, Selector, Formals, Locals, Body),
        Installed).

% @latex equation:declaration-elaboration
% @variant member-slot
% @lean Newspeak.deriveMemberDeclaration
% @mode derive_member_declaration(+,+,+,+,+,+,+,+,-)
derive_member_declaration(
    derive_member_slot(
        DeclarationProof, MethodsProof, InstallationProof),
    Identification, _Services, _Context, Owner, Mixin, Image,
    surface_slot(Span, AccessOption, Name, Mutability, _Initializer),
    Installed) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, slot, Declaration),
    access_or_protected(AccessOption, Access),
    ordinary_slot_methods(
        MethodsProof, Declaration, Owner, Name, Access, Mutability, Methods),
    add_derived_methods(
        InstallationProof, Image, Mixin, Methods, Installed).

% @latex equation:declaration-elaboration
% @variant member-lazy-slot
% @lean Newspeak.deriveMemberDeclaration
% @mode derive_member_declaration(+,+,+,+,+,+,+,+,-)
derive_member_declaration(
    derive_member_lazy_slot(
        DeclarationProof, ExpressionProof,
        MethodsProof, InstallationProof),
    Identification, Services, Context, Owner, Mixin, Image,
    surface_lazy_slot(Span, AccessOption, Name, Mutability, Initializer),
    Installed) :-
    declaration_identity_at(
        DeclarationProof, Identification, Span, lazy_slot, Declaration),
    access_or_protected(AccessOption, Access),
    elaborate_expression(
        ExpressionProof, Services, Context, Initializer, CoreInitializer),
    lazy_slot_methods(
        MethodsProof, Declaration, Owner, Name, Access, Mutability,
        CoreInitializer, Methods),
    add_derived_methods(
        InstallationProof, Image, Mixin, Methods, Installed).

% @latex equation:declaration-elaboration
% @variant member-nested-class-deferred
% @lean Newspeak.deriveMemberDeclaration
% @mode derive_member_declaration(+,+,+,+,+,+,+,+,-)
derive_member_declaration(
    derive_member_nested_class_deferred,
    _Identification, _Services, _Context, _Owner, _Mixin, Image,
    surface_nested_class(_Span, _Access, _Declaration), Image).

% @latex equation:declaration-elaboration
% @variant members-empty
% @lean Newspeak.deriveMemberDeclarations
% @mode derive_member_declarations(+,+,+,+,+,+,+,+,-)
derive_member_declarations(
    derive_members_empty,
    _Identification, _Services, _Context, _Owner, _Mixin, Image, [], Image).

% @latex equation:declaration-elaboration
% @variant members-cons
% @lean Newspeak.deriveMemberDeclarations
% @mode derive_member_declarations(+,+,+,+,+,+,+,+,-)
derive_member_declarations(
    derive_members_cons(MemberProof, RemainingProof),
    Identification, Services, Context, Owner, Mixin, Image,
    [Declaration|Remaining], Installed) :-
    derive_member_declaration(
        MemberProof, Identification, Services, Context, Owner, Mixin,
        Image, Declaration, Next),
    derive_member_declarations(
        RemainingProof, Identification, Services, Context, Owner, Mixin,
        Next, Remaining, Installed).

% --------------------------------------------------------------------------
% Class, mixin, object, and complete Program derivation
% --------------------------------------------------------------------------

% @latex equation:front-end-mixin-fold
% @variant message-template
% @lean Newspeak.elaborateMessageTemplate
% @mode elaborate_message_template(+,+,+,+,-)
elaborate_message_template(
    elaborate_message_template(DerivationProof), Services, Context,
    Clause, Message).

% @latex equation:front-end-class-body-elaboration
% @variant direct-default-structure
% @lean Newspeak.directClassStructure
% @mode direct_class_structure(+,+,-)
direct_class_structure(
    direct_default_structure,
    surface_default_inheritance(_Span, Structure), Structure).

% @latex equation:front-end-class-body-elaboration
% @variant direct-explicit-structure
% @lean Newspeak.directClassStructure
% @mode direct_class_structure(+,+,-)
direct_class_structure(
    direct_explicit_structure,
    surface_explicit_inheritance(_Span, _Receiver, _Initializer, Structure),
    Structure).

% @latex equation:front-end-default-superclass
% @variant direct-default-syntax
% @lean Newspeak.directSuperclassSyntax
% @mode direct_superclass_syntax(+,+,-)
direct_superclass_syntax(
    direct_default_syntax,
    surface_default_inheritance(_Span, _Structure), implicit_superclass).

% @latex equation:front-end-default-superclass
% @variant direct-explicit-syntax
% @lean Newspeak.directSuperclassSyntax
% @mode direct_superclass_syntax(+,+,-)
direct_superclass_syntax(
    direct_explicit_syntax,
    surface_explicit_inheritance(
        _Span, _Receiver, _Initializer, _Structure),
    explicit_superclass).

% @latex equation:front-end-default-superclass
% @variant direct-mixin-syntax
% @lean Newspeak.directSuperclassSyntax
% @mode direct_superclass_syntax(+,+,-)
direct_superclass_syntax(
    direct_mixin_syntax,
    surface_mixin_chain(
        _Span, _Receiver, _Initializer, _Additional, _Structure),
    explicit_superclass).

% @latex equation:front-end-default-superclass
% @variant direct-default-message
% @lean Newspeak.directSuperclassMessage
% @mode direct_superclass_message(+,+,+,+,-)
direct_superclass_message(
    direct_default_message, _Services, _Context,
    surface_default_inheritance(_Span, _Structure),
    message_template(selector(new), [])).

% @latex equation:front-end-default-superclass
% @variant direct-explicit-message
% @lean Newspeak.directSuperclassMessage
% @mode direct_superclass_message(+,+,+,+,-)
direct_superclass_message(
    direct_explicit_message(MessageProof), Services, Context,
    surface_explicit_inheritance(
        _Span, _Receiver, Initializer, _Structure), Message) :-
    elaborate_message_template(
        MessageProof, Services, Context, Initializer, Message).

% @latex equation:front-end-default-superclass
% @variant direct-mixin-message
% @lean Newspeak.directSuperclassMessage
% @mode direct_superclass_message(+,+,+,+,-)
direct_superclass_message(
    direct_mixin_message(MessageProof), Services, Context,
    surface_mixin_chain(
        _Span, _Receiver, Initializer, _Additional, _Structure), Message) :-
    elaborate_message_template(
        MessageProof, Services, Context, Initializer, Message).

% @latex equation:front-end-default-superclass
% @variant direct-default-expression
% @lean Newspeak.directSuperclassExpression
% @mode direct_superclass_expression(+,+,+,+,-)
direct_superclass_expression(
    direct_default_expression(DefaultProof), Services, Context,
    surface_default_inheritance(_Span, _Structure), Superclass) :-
    default_superclass_application(
        DefaultProof, Services, Context, Superclass).

% @latex equation:front-end-default-superclass
% @variant direct-explicit-expression
% @lean Newspeak.directSuperclassExpression
% @mode direct_superclass_expression(+,+,+,+,-)
direct_superclass_expression(
    direct_explicit_expression(ExpressionProof), Services, Context,
    surface_explicit_inheritance(
        _Span, Receiver, _Initializer, _Structure), Superclass) :-
    elaborate_expression(
        ExpressionProof, Services, Context, Receiver, Superclass).

% @latex equation:front-end-default-superclass
% @variant direct-mixin-expression
% @lean Newspeak.directSuperclassExpression
% @mode direct_superclass_expression(+,+,+,+,-)
direct_superclass_expression(
    direct_mixin_expression(ExpressionProof), Services, Context,
    surface_mixin_chain(
        _Span, Receiver, _Initializer, _Additional, _Structure), Superclass) :-
    elaborate_expression(
        ExpressionProof, Services, Context, Receiver, Superclass).

% @latex equation:front-end-object-elaboration
% @variant owner-activation
% @lean Newspeak.objectLiteralOwnerFromContext
% @mode object_literal_owner_from_context(+,+,-)
object_literal_owner_from_context(
    object_owner_activation,
    elaboration_context(
        _ClassBody, some(_Activation), _Kind, _Immediate,
        _Binders, _LocalReturn, _NonlocalReturn),
    activation_owner).

% @latex equation:front-end-object-elaboration
% @variant owner-class
% @lean Newspeak.objectLiteralOwnerFromContext
% @mode object_literal_owner_from_context(+,+,-)
object_literal_owner_from_context(
    object_owner_class,
    elaboration_context(
        some(named_class(_Class)), none, _Kind, _Immediate,
        _Binders, _LocalReturn, _NonlocalReturn),
    class_owner).

% @latex equation:front-end-object-elaboration
% @variant owner-object
% @lean Newspeak.objectLiteralOwnerFromContext
% @mode object_literal_owner_from_context(+,+,-)
object_literal_owner_from_context(
    object_owner_object,
    elaboration_context(
        some(object_literal(_Object)), none, _Kind, _Immediate,
        _Binders, _LocalReturn, _NonlocalReturn),
    object_literal_owner).

% @latex equation:front-end-object-elaboration
% @variant owner-top
% @lean Newspeak.objectLiteralOwnerFromContext
% @mode object_literal_owner_from_context(+,+,-)
object_literal_owner_from_context(
    object_owner_top,
    elaboration_context(
        none, none, _Kind, _Immediate,
        _Binders, _LocalReturn, _NonlocalReturn),
    top_owner).

% @latex equation:front-end-object-elaboration
% @variant implicit-header-structure
% @lean Newspeak.objectHeaderStructure
% @mode object_header_structure(+,+,-)
object_header_structure(
    implicit_header_structure,
    surface_implicit_header(_Span, Structure), Structure).

% @latex equation:front-end-object-elaboration
% @variant explicit-header-structure
% @lean Newspeak.objectHeaderStructure
% @mode object_header_structure(+,+,-)
object_header_structure(
    explicit_header_structure,
    surface_explicit_header(_Span, _Receiver, _Initializer, Structure),
    Structure).

% @latex equation:front-end-default-superclass
% @variant object-implicit-syntax
% @lean Newspeak.objectHeaderSuperclassSyntax
% @mode object_header_superclass_syntax(+,+,-)
object_header_superclass_syntax(
    object_implicit_syntax,
    surface_implicit_header(_Span, _Structure), implicit_superclass).

% @latex equation:front-end-default-superclass
% @variant object-explicit-syntax
% @lean Newspeak.objectHeaderSuperclassSyntax
% @mode object_header_superclass_syntax(+,+,-)
object_header_superclass_syntax(
    object_explicit_syntax,
    surface_explicit_header(
        _Span, _Receiver, _Initializer, _Structure), explicit_superclass).

% @latex equation:front-end-default-superclass
% @variant object-implicit-expression
% @lean Newspeak.objectHeaderSuperclass
% @mode object_header_superclass(+,+,+,+,-)
object_header_superclass(
    object_implicit_expression(DefaultProof), Services, Context,
    surface_implicit_header(_Span, _Structure), Superclass) :-
    default_superclass_application(
        DefaultProof, Services, Context, Superclass).

% @latex equation:front-end-default-superclass
% @variant object-explicit-expression
% @lean Newspeak.objectHeaderSuperclass
% @mode object_header_superclass(+,+,+,+,-)
object_header_superclass(
    object_explicit_expression(ExpressionProof), Services, Context,
    surface_explicit_header(
        _Span, Receiver, _Initializer, _Structure), Superclass) :-
    elaborate_expression(
        ExpressionProof, Services, Context, Receiver, Superclass).

% @latex equation:front-end-default-superclass
% @variant object-implicit-message
% @lean Newspeak.objectHeaderSuperclassMessage
% @mode object_header_superclass_message(+,+,+,+,-)
object_header_superclass_message(
    object_implicit_message, _Services, _Context,
    surface_implicit_header(_Span, _Structure),
    message_template(selector(new), [])).

% @latex equation:front-end-default-superclass
% @variant object-explicit-message
% @lean Newspeak.objectHeaderSuperclassMessage
% @mode object_header_superclass_message(+,+,+,+,-)
object_header_superclass_message(
    object_explicit_message(MessageProof), Services, Context,
    surface_explicit_header(
        _Span, _Receiver, Initializer, _Structure), Message) :-
    elaborate_message_template(
        MessageProof, Services, Context, Initializer, Message).

% @latex equation:front-end-mixin-fold
% @variant anonymous-application
% @lean Newspeak.deriveAnonymousApplication
% @mode derive_anonymous_application(+,+,+,+,+,+,+,+,+,+,+,-)
derive_anonymous_application(
    derive_anonymous_application(DerivationProof), Config, Identification,
    Enclosing, Position, OwnerKind, Context, Image, Superclass,
    SuperclassInitializer, Head,
    application_fold(NextImage, NextSuperclass, NextInitializer)).

% @latex equation:front-end-mixin-fold
% @variant fold-empty
% @lean Newspeak.foldAnonymousApplications
% @mode fold_anonymous_applications(+,+,+,+,+,+,+,+,+,+,+,-)
fold_anonymous_applications(
    fold_anonymous_empty, _Config, _Identification, _Enclosing, _OwnerKind,
    _Context, _Position, Image, Superclass, Initializer, [],
    application_fold(Image, Superclass, Initializer)).

% @latex equation:front-end-mixin-fold
% @variant fold-cons
% @lean Newspeak.foldAnonymousApplications
% @mode fold_anonymous_applications(+,+,+,+,+,+,+,+,+,+,+,-)
fold_anonymous_applications(
    fold_anonymous_cons(ApplicationProof, SuccessorProof, RemainingProof),
    Config, Identification, Enclosing, OwnerKind, Context, Position,
    Image, Superclass, Initializer, [Head|Remaining], Output) :-
    derive_anonymous_application(
        ApplicationProof, Config, Identification, Enclosing, Position,
        OwnerKind, Context, Image, Superclass, Initializer, Head,
        application_fold(NextImage, NextSuperclass, NextInitializer)),
    natural_successor(SuccessorProof, Position, NextPosition),
    fold_anonymous_applications(
        RemainingProof, Config, Identification, Enclosing, OwnerKind, Context,
        NextPosition, NextImage, NextSuperclass, NextInitializer,
        Remaining, Output).

% @latex equation:front-end-bodyless-mixin-elaboration
% @lean Newspeak.deriveBodylessMixinChainInto
% @mode derive_bodyless_mixin_chain_into(+,+,+,+,+,+,+,+,-)
derive_bodyless_mixin_chain_into(
    derive_bodyless_mixin_chain_into(DerivationProof), Config, ArtifactConfig,
    Identification, Context, OwnerKind, Image, Declaration,
    image_expression(Complete, Expression)).

% @latex equation:front-end-class-body-elaboration
% @lean Newspeak.deriveClassDeclarationIntoWithFuel
% @mode derive_class_declaration_into_with_fuel(+,+,+,+,+,+,+,+,+,-)
derive_class_declaration_into_with_fuel(
    derive_class_declaration_into(DerivationProof), Config, ArtifactConfig,
    Identification, Fuel, Context, OwnerKind, Image, Declaration,
    image_expression(Complete, Expression)).

% @latex equation:declaration-elaboration
% @variant nested-class-list
% @lean Newspeak.deriveNestedClassDeclarationsWithFuel
% @mode derive_nested_class_declarations_with_fuel(+,+,+,+,+,+,+,+,+,+,-)
derive_nested_class_declarations_with_fuel(
    derive_nested_classes(DerivationProof), Config, ArtifactConfig,
    Identification, Fuel, Context, Owner, Mixin, Image, Declarations,
    Complete).

% @latex equation:front-end-object-elaboration
% @lean Newspeak.deriveObjectLiteralInto
% @mode derive_object_literal_into(+,+,+,+,+,+,+,+,-)
derive_object_literal_into(
    derive_object_literal(DerivationProof), Config, ArtifactConfig,
    Identification, Context, Image, Span, Header,
    image_expression(Complete, Expression)).

% @latex equation:derived-program-indexes
% @variant structural-contents
% @lean Newspeak.deriveStructuralClassDeclarationContents
% @mode derive_structural_class_declaration_contents(+,+,+,+,+,+,+,-)
derive_structural_class_declaration_contents(
    derive_structural_contents(DerivationProof), Config, ArtifactConfig,
    Identification, Context, Image, Declaration, Complete).

% @latex equation:front-end-bodied-mixin-elaboration
% @lean Newspeak.deriveBodiedMixinChainImage
% @mode derive_bodied_mixin_chain_image(+,+,+,+,+,+,+,+,-)
derive_bodied_mixin_chain_image(
    derive_bodied_mixin_image(DerivationProof), Config, ArtifactConfig,
    Identification, Context, OwnerKind, Image, Declaration,
    image_expression(Complete, Expression)).

% The following projections make the outer Program constructors readable
% without assuming a concrete Prolog representation for configuration records.

% @latex equation:front-end-phase-behavior
% @variant artifact-fuel
% @lean Newspeak.EmbeddedArtifactConfig.fuel
% @mode embedded_artifact_fuel(+,+,-)
embedded_artifact_fuel(
    embedded_artifact_fuel(FuelProof), ArtifactConfig, Fuel).

% @latex equation:front-end-default-superclass
% @variant top-context
% @lean Newspeak.topElaborationContext
% @mode top_elaboration_context(-)
top_elaboration_context(top_elaboration_context).

% @latex equation:derived-program-indexes
% @variant empty-image
% @lean Newspeak.DerivedProgramImage.empty
% @mode empty_derived_program_image(-)
empty_derived_program_image(empty_derived_program_image).

% @latex equation:declaration-derivation
% @variant base-program
% @lean Newspeak.DirectDerivationConfig.baseProgram
% @mode direct_derivation_base_program(+,+,-)
direct_derivation_base_program(
    direct_derivation_base_program(BaseProof), Config, BaseProgram).

% @latex equation:declaration-derivation
% @variant install-image
% @lean Newspeak.DerivedProgramImage.install
% @mode derived_program_image_install(+,+,+,-)
derived_program_image_install(
    derived_program_image_install(InstallationProof),
    Image, BaseProgram, Program).

% @latex equation:compilation-unit
% @variant declaration-projection
% @lean Newspeak.SurfaceCompilationUnit.declaration
% @mode surface_compilation_unit_declaration(+,+,-)
surface_compilation_unit_declaration(
    compilation_unit_declaration(ProjectionProof), Unit, Declaration).

% @latex equation:front-end-bodyless-mixin-elaboration
% @variant complete-program
% @lean Newspeak.deriveBodylessMixinChainProgram
% @mode derive_bodyless_mixin_chain_program(+,+,+,+,+,-)
derive_bodyless_mixin_chain_program(
    bodyless_mixin_program(
        ProjectionProof, ImageProof, BaseProof, InstallationProof),
    Config, ArtifactConfig, Unit, Identification,
    program_expression(Program, Expression)) :-
    top_elaboration_context(Context),
    empty_derived_program_image(EmptyImage),
    surface_compilation_unit_declaration(
        ProjectionProof, Unit, Declaration),
    derive_bodyless_mixin_chain_into(
        ImageProof, Config, ArtifactConfig, Identification, Context,
        top_owner, EmptyImage, Declaration,
        image_expression(Complete, Expression)),
    direct_derivation_base_program(BaseProof, Config, BaseProgram),
    derived_program_image_install(
        InstallationProof, Complete, BaseProgram, Program).

% @latex equation:front-end-bodied-mixin-elaboration
% @variant complete-program
% @lean Newspeak.deriveBodiedMixinChainProgram
% @mode derive_bodied_mixin_chain_program(+,+,+,+,+,-)
derive_bodied_mixin_chain_program(
    bodied_mixin_program(
        ProjectionProof, ImageProof, ContentsProof,
        BaseProof, InstallationProof),
    Config, ArtifactConfig, Unit, Identification,
    program_expression(Program, Expression)) :-
    top_elaboration_context(Context),
    empty_derived_program_image(EmptyImage),
    surface_compilation_unit_declaration(
        ProjectionProof, Unit, Declaration),
    derive_bodied_mixin_chain_image(
        ImageProof, Config, ArtifactConfig, Identification, Context,
        top_owner, EmptyImage, Declaration,
        image_expression(Image, Expression)),
    derive_structural_class_declaration_contents(
        ContentsProof, Config, ArtifactConfig, Identification, Context,
        Image, Declaration, Complete),
    direct_derivation_base_program(BaseProof, Config, BaseProgram),
    derived_program_image_install(
        InstallationProof, Complete, BaseProgram, Program).

% @latex equation:declaration-derivation
% @variant structural-class-program
% @lean Newspeak.deriveClassProgramWithStructuralArtifacts
% @mode derive_structural_class_program(+,+,+,+,+,-)
derive_structural_class_program(
    structural_class_program(
        FuelProof, ProjectionProof, ClassProof, ContentsProof,
        BaseProof, InstallationProof),
    Config, ArtifactConfig, Unit, Identification,
    program_expression(Program, Expression)) :-
    embedded_artifact_fuel(FuelProof, ArtifactConfig, Fuel),
    top_elaboration_context(Context),
    empty_derived_program_image(EmptyImage),
    surface_compilation_unit_declaration(
        ProjectionProof, Unit, Declaration),
    derive_class_declaration_into_with_fuel(
        ClassProof, Config, ArtifactConfig, Identification, Fuel, Context,
        top_owner, EmptyImage, Declaration,
        image_expression(Image, Expression)),
    derive_structural_class_declaration_contents(
        ContentsProof, Config, ArtifactConfig, Identification, Context,
        Image, Declaration, Complete),
    direct_derivation_base_program(BaseProof, Config, BaseProgram),
    derived_program_image_install(
        InstallationProof, Complete, BaseProgram, Program).

% @latex equation:declaration-derivation
% @variant complete-bodyless-mixin
% @lean Newspeak.deriveCompleteClassProgram
% @mode derive_complete_class_program(+,+,+,+,+,-)
derive_complete_class_program(
    complete_bodyless_mixin(ProjectionProof, ProgramProof),
    Config, ArtifactConfig, Unit, Identification, Output) :-
    surface_compilation_unit_declaration(
        ProjectionProof, Unit,
        surface_class_declaration(
            _Span, _Name, _Selector, _Formals,
            surface_mixin_chain(
                _InheritanceSpan, _Receiver, _Initializer,
                _Additional, none))),
    derive_bodyless_mixin_chain_program(
        ProgramProof, Config, ArtifactConfig, Unit, Identification, Output).

% @latex equation:declaration-derivation
% @variant complete-bodied-mixin
% @lean Newspeak.deriveCompleteClassProgram
% @mode derive_complete_class_program(+,+,+,+,+,-)
derive_complete_class_program(
    complete_bodied_mixin(ProjectionProof, ProgramProof),
    Config, ArtifactConfig, Unit, Identification, Output) :-
    surface_compilation_unit_declaration(
        ProjectionProof, Unit,
        surface_class_declaration(
            _Span, _Name, _Selector, _Formals,
            surface_mixin_chain(
                _InheritanceSpan, _Receiver, _Initializer,
                _Additional, some(_Body)))),
    derive_bodied_mixin_chain_program(
        ProgramProof, Config, ArtifactConfig, Unit, Identification, Output).

% @latex equation:declaration-derivation
% @variant complete-default-class
% @lean Newspeak.deriveCompleteClassProgram
% @mode derive_complete_class_program(+,+,+,+,+,-)
derive_complete_class_program(
    complete_default_class(ProjectionProof, ProgramProof),
    Config, ArtifactConfig, Unit, Identification, Output) :-
    surface_compilation_unit_declaration(
        ProjectionProof, Unit,
        surface_class_declaration(
            _Span, _Name, _Selector, _Formals,
            surface_default_inheritance(_InheritanceSpan, _Body))),
    derive_structural_class_program(
        ProgramProof, Config, ArtifactConfig, Unit, Identification, Output).

% @latex equation:declaration-derivation
% @variant complete-explicit-class
% @lean Newspeak.deriveCompleteClassProgram
% @mode derive_complete_class_program(+,+,+,+,+,-)
derive_complete_class_program(
    complete_explicit_class(ProjectionProof, ProgramProof),
    Config, ArtifactConfig, Unit, Identification, Output) :-
    surface_compilation_unit_declaration(
        ProjectionProof, Unit,
        surface_class_declaration(
            _Span, _Name, _Selector, _Formals,
            surface_explicit_inheritance(
                _InheritanceSpan, _Receiver, _Initializer, _Body))),
    derive_structural_class_program(
        ProgramProof, Config, ArtifactConfig, Unit, Identification, Output).

% --------------------------------------------------------------------------
% Actor turns: entry and lifted sequential execution
% --------------------------------------------------------------------------

% Actor worlds use the same extensible named-field representation as programs
% and heaps.  The field names below are the projections of Equation (10.1).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld
% @mode actor_world_field(+,+,-)
actor_world_field(actor_world(Fields), Name, Value) :-
    store_lookup(Fields, Name, some(Value)).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld
% @mode actor_world_install_field(+,+,+,-)
actor_world_install_field(
    actor_world(Fields), Name, Value, actor_world(NewFields)) :-
    store_install(Fields, Name, Value, NewFields).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.program
% @mode actor_world_program(+,-)
actor_world_program(World, Program) :-
    actor_world_field(World, program, Program).

% @latex equation:actor-run-state
% @lean Newspeak.ActorWorld.runStates
% @mode actor_run_state(+,+,-)
actor_run_state(World, Actor, Result) :-
    actor_world_field(World, run_states, RunStates),
    store_lookup(RunStates, Actor, Result).

% @latex equation:current-activation
% @variant running
% @lean Newspeak.PrologBridge.PrologCurrentActorActivation.running
% @mode current_actor_activation(+,+,-)
current_actor_activation(World, Actor, Activation) :-
    actor_run_state(
        World, Actor,
        some(running_turn(
            sequential_config(
                _Allocation,
                activation_stack_push(
                    _Rest, activation_frame(Activation, _Frames)),
                _Control),
            _ReplyPromise, _TriggeringEvent))).

% @latex equation:current-activation
% @variant paused
% @lean Newspeak.PrologBridge.PrologCurrentActorActivation.paused
% @mode current_actor_activation(+,+,-)
current_actor_activation(World, Actor, Activation) :-
    actor_run_state(
        World, Actor,
        some(paused_turn(
            sequential_config(
                _Allocation,
                activation_stack_push(
                    _Rest, activation_frame(Activation, _Frames)),
                _Control),
            _ReplyPromise, _TriggeringEvent, _PauseToken, _StopReason))).

% @latex equation:decode-control-image
% @variant active-top
% @lean Newspeak.PrologBridge.PrologDecodeControlImageAux.activeTop
% @mode decode_control_image_aux(+,+,-,-)
decode_control_image_aux(
    Built,
    [resolved_frame_image(Activation, active_control(Frames, Term))],
    activation_stack_push(Built, activation_frame(Activation, Frames)),
    Term).

% @latex equation:decode-control-image
% @variant suspended-lower-frame
% @lean Newspeak.PrologBridge.PrologDecodeControlImageAux.suspended
% @mode decode_control_image_aux(+,+,-,-)
decode_control_image_aux(
    Built,
    [resolved_frame_image(
        Activation, suspended_control(Frames)), Next | Remaining],
    Stack, Term) :-
    decode_control_image_aux(
        activation_stack_push(Built, activation_frame(Activation, Frames)),
        [Next | Remaining], Stack, Term).

% @latex equation:decode-control-image
% @variant wrapper
% @lean Newspeak.PrologBridge.PrologDecodeControlImage.decode
% @mode decode_control_image(+,-,-)
decode_control_image(Images, Stack, Term) :-
    decode_control_image_aux(
        activation_stack_empty, Images, Stack, Term).

% @latex equation:actor-stack-snapshot
% @variant suspended-empty
% @lean Newspeak.PrologBridge.PrologSuspendedControlImage.empty
% @mode suspended_control_image(+,-)
suspended_control_image(activation_stack_empty, []).

% @latex equation:actor-stack-snapshot
% @variant suspended-push
% @lean Newspeak.PrologBridge.PrologSuspendedControlImage.push
% @mode suspended_control_image(+,-)
suspended_control_image(
    activation_stack_push(Rest, activation_frame(Activation, Frames)), Images) :-
    suspended_control_image(Rest, Earlier),
    list_append(Earlier,
                [resolved_frame_image(Activation, suspended_control(Frames))],
                Images).

% @latex equation:actor-stack-snapshot
% @variant control-image
% @lean Newspeak.PrologBridge.PrologControlImage.nonempty
% @mode activation_stack_control_image(+,+,-)
activation_stack_control_image(
    activation_stack_push(Rest, activation_frame(Activation, Frames)), Term,
    Images) :-
    suspended_control_image(Rest, Earlier),
    list_append(Earlier,
                [resolved_frame_image(Activation, active_control(Frames, Term))],
                Images).

% @latex equation:actor-stack-snapshot
% @variant reify-empty
% @lean Newspeak.PrologBridge.PrologReifyDebugFrames.empty
% @mode reify_debug_frames(+,+,-)
reify_debug_frames(_Heap, [], []).

% @latex equation:actor-stack-snapshot
% @variant reify-step
% @lean Newspeak.PrologBridge.PrologReifyDebugFrames.step
% @mode reify_debug_frames(+,+,-)
reify_debug_frames(
    Heap, [resolved_frame_image(Activation, Control) | Remaining],
    [debug_frame_image(Activation, Definition, Control) | Tail]) :-
    heap_field(Heap, activations, Activations),
    store_lookup(Activations, Activation, some(Definition)),
    reify_debug_frames(Heap, Remaining, Tail).

% @latex equation:actor-stack-snapshot
% @variant running
% @lean Newspeak.PrologBridge.PrologActorStackSnapshot.running
% @mode actor_stack_snapshot(+,+,-)
actor_stack_snapshot(World, Actor,
                     actor_stack_snapshot(running_mode, Frames)) :-
    actor_run_state(
        World, Actor,
        some(running_turn(
            sequential_config(Allocation, Stack, Term), _Reply, _Event))),
    activation_stack_control_image(Stack, Term, Controls),
    allocation_state_heap(Allocation, Heap),
    reify_debug_frames(Heap, Controls, Frames).

% @latex equation:actor-stack-snapshot
% @variant paused
% @lean Newspeak.PrologBridge.PrologActorStackSnapshot.paused
% @mode actor_stack_snapshot(+,+,-)
actor_stack_snapshot(
    World, Actor, actor_stack_snapshot(paused_mode(Token, Reason), Frames)) :-
    actor_run_state(
        World, Actor,
        some(paused_turn(
            sequential_config(Allocation, Stack, Term), _Reply, _Event,
            Token, Reason))),
    activation_stack_control_image(Stack, Term, Controls),
    allocation_state_heap(Allocation, Heap),
    reify_debug_frames(Heap, Controls, Frames).

% @latex equation:live-activation-control
% @lean Newspeak.PrologBridge.PrologLiveActivationControl.found
% @mode live_activation_control(+,+,-)
live_activation_control(World, Activation, Control) :-
    live_activation_control_application(
        live_activation_control(World, Activation, Control),
        World, Activation, Control).

% @latex equation:live-activation-control
% @variant application
% @lean Newspeak.ActorWorld.liveActivationControl?
% @mode live_activation_control_application(+,+,+,+)
live_activation_control_application(
    live_activation_control(World, Activation, Control),
    World, Activation, Control).

% @latex equation:debug-activation-descriptor
% @lean Newspeak.PrologBridge.PrologDebugActivationDescriptor.describe
% @mode debug_activation_descriptor(+,+,-)
debug_activation_descriptor(
    World, Activation,
    debug_activation_descriptor(
        reflection_activation(Location, Definition), OptionalControl)) :-
    locate_activation_id_application(
        locate_activation_id(World, Activation, Location),
        World, Activation, Location),
    actor_world_heap_at(World, Location, Heap),
    heap_field(Heap, activations, Activations),
    store_lookup(Activations, Activation, some(Definition)),
    live_activation_control_option_application(
        live_activation_control_option(World, Activation, OptionalControl),
        World, Activation, OptionalControl).

% @latex equation:debug-activation-descriptor
% @variant optional-control-application
% @lean Newspeak.ActorWorld.liveActivationControl?
% @mode live_activation_control_option_application(+,+,+,+)
live_activation_control_option_application(
    live_activation_control_option(World, Activation, OptionalControl),
    World, Activation, OptionalControl).

% @latex equation:promote-demote-frame-control
% @variant promote
% @lean Newspeak.PrologBridge.PrologPromoteFrame.suspended
% @mode promote_frame(+,+,-)
promote_frame(
    frame_template(Key, Record, suspended_control(Frames)), Value,
    frame_template(Key, Record, active_control(Frames, Value))).

% @latex equation:promote-demote-frame-control
% @variant demote
% @lean Newspeak.PrologBridge.PrologDemoteFrame.active
% @mode demote_frame(+,-)
demote_frame(
    frame_template(Key, Record, active_control(Frames, _Term)),
    frame_template(Key, Record, suspended_control(Frames))).

% @latex equation:pop-stack-frames
% @variant promote-top-single
% @lean Newspeak.PrologBridge.PrologPromoteTopFrame.single
% @mode promote_top_frame(+,+,-)
promote_top_frame([Frame], Value, [Promoted]) :-
    promote_frame(Frame, Value, Promoted).

% @latex equation:pop-stack-frames
% @variant promote-top-step
% @lean Newspeak.PrologBridge.PrologPromoteTopFrame.step
% @mode promote_top_frame(+,+,-)
promote_top_frame([Frame, Next | Remaining], Value, [Frame | Promoted]) :-
    promote_top_frame([Next | Remaining], Value, Promoted).

% @latex equation:pop-stack-frames
% @variant remove-top-single
% @lean Newspeak.PrologBridge.PrologRemoveTopFrame.single
% @mode remove_top_frame(+,-)
remove_top_frame([_Frame], []).

% @latex equation:pop-stack-frames
% @variant remove-top-step
% @lean Newspeak.PrologBridge.PrologRemoveTopFrame.step
% @mode remove_top_frame(+,-)
remove_top_frame([Frame, Next | Remaining], [Frame | Shortened]) :-
    remove_top_frame([Next | Remaining], Shortened).

% @latex equation:pop-stack-frames
% @variant zero
% @lean Newspeak.PrologBridge.PrologPopStackFrames.zero
% @mode pop_stack_frames(+,+,+,-)
pop_stack_frames(Stack, zero, Value, Result) :-
    promote_top_frame(Stack, Value, Result).

% @latex equation:pop-stack-frames
% @variant successor
% @lean Newspeak.PrologBridge.PrologPopStackFrames.successor
% @mode pop_stack_frames(+,+,+,-)
pop_stack_frames(Stack, succ(Count), Value, Result) :-
    remove_top_frame(Stack, Shortened),
    pop_stack_frames(Shortened, Count, Value, Result).

% @latex equation:push-stack-frame
% @variant demote-top-single
% @lean Newspeak.PrologBridge.PrologDemoteTopFrame.single
% @mode demote_top_frame(+,-)
demote_top_frame([Frame], [Demoted]) :-
    demote_frame(Frame, Demoted).

% @latex equation:push-stack-frame
% @variant demote-top-step
% @lean Newspeak.PrologBridge.PrologDemoteTopFrame.step
% @mode demote_top_frame(+,-)
demote_top_frame([Frame, Next | Remaining], [Frame | Demoted]) :-
    demote_top_frame([Next | Remaining], Demoted).

% @latex equation:push-stack-frame
% @lean Newspeak.PrologBridge.PrologPushStackFrame.active
% @mode push_stack_frame(+,+,-)
push_stack_frame(
    Stack, frame_template(Key, Record, active_control(Frames, Term)),
    Result) :-
    demote_top_frame(Stack, Demoted),
    list_append(
        Demoted, [frame_template(
            Key, Record, active_control(Frames, Term))], Result).

% @latex equation:frame-current-term-and-location
% @variant current-term-active
% @lean Newspeak.PrologBridge.PrologFrameCurrentTerm.active
% @mode frame_current_term(+,-)
frame_current_term(active_control(_Frames, Term), active_term(Term)).

% @latex equation:frame-current-term-and-location
% @variant current-term-suspended
% @lean Newspeak.PrologBridge.PrologFrameCurrentTerm.suspended
% @mode frame_current_term(+,-)
frame_current_term(suspended_control(_Frames), await_result).

% The following two predicates are proof-carrying applications of the
% elaborator/compiler control maps retained with the frame material.

% @latex equation:frame-current-term-and-location
% @variant site-application
% @lean Newspeak.PrologBridge.PrologControlSiteApplication.witness
% @mode control_site_application(+,+,+,+,+)
control_site_application(
    control_site_application(ControlMap, Frames, Term, Location),
    ControlMap, Frames, Term, Location).

% @latex equation:frame-current-term-and-location
% @variant resume-site-application
% @lean Newspeak.PrologBridge.PrologControlResumeApplication.witness
% @mode control_resume_application(+,+,+,+)
control_resume_application(
    control_resume_application(ControlMap, Frames, Location),
    ControlMap, Frames, Location).

% @latex equation:frame-current-term-and-location
% @variant location-active
% @lean Newspeak.PrologBridge.PrologFrameControlLocation.active
% @mode frame_control_location(+,+,+,+,-)
frame_control_location(
    ControlMap, SiteApplication, _ResumeApplication,
    active_control(Frames, Term), Location) :-
    control_site_application(
        SiteApplication, ControlMap, Frames, Term, Location).

% @latex equation:frame-current-term-and-location
% @variant location-suspended
% @lean Newspeak.PrologBridge.PrologFrameControlLocation.suspended
% @mode frame_control_location(+,+,+,+,-)
frame_control_location(
    ControlMap, _SiteApplication, ResumeApplication,
    suspended_control(Frames), Location) :-
    control_resume_application(
        ResumeApplication, ControlMap, Frames, Location).

% @latex equation:stack-template-record-locations
% @variant empty
% @lean Newspeak.PrologBridge.PrologStackTemplateRecordLocations.empty
% @mode stack_template_record_locations(+,-)
stack_template_record_locations([], []).

% @latex equation:stack-template-record-locations
% @variant retained
% @lean Newspeak.PrologBridge.PrologStackTemplateRecordLocations.retained
% @mode stack_template_record_locations(+,-)
stack_template_record_locations(
    [frame_template(retain(Activation), _Record, _Control) | Remaining],
    [activation_record_location(Activation) | Locations]) :-
    stack_template_record_locations(Remaining, Locations).

% @latex equation:stack-template-record-locations
% @variant fresh
% @lean Newspeak.PrologBridge.PrologStackTemplateRecordLocations.fresh
% @mode stack_template_record_locations(+,-)
stack_template_record_locations(
    [frame_template(fresh_frame(_Key), _Record, _Control) | Remaining],
    Locations) :-
    stack_template_record_locations(Remaining, Locations).

% Per-heap population filters are executable Lean functions.  Their explicit
% graph terms expose the implementation-chosen finite-store order; the cohort
% traversal itself is expanded below.

% @latex equation:all-instances-of
% @variant heap-application
% @lean Newspeak.PrologBridge.PrologHeapAllInstances.application
% @mode heap_all_instances(+,+,+,-)
heap_all_instances(
    heap_all_instances(Heap, Class, Values), Heap, Class, Values).

% @latex equation:all-instances-of
% @variant actor-empty
% @lean Newspeak.PrologBridge.PrologActorInstancesOf.empty
% @mode actor_instances_of(+,+,+,-)
actor_instances_of(_World, _Class, [], []).

% @latex equation:all-instances-of
% @variant actor-absent
% @lean Newspeak.PrologBridge.PrologActorInstancesOf.absent
% @mode actor_instances_of(+,+,+,-)
actor_instances_of(World, Class, [Actor | Remaining], Values) :-
    actor_allocation(World, Actor, none),
    actor_instances_of(World, Class, Remaining, Values).

% @latex equation:all-instances-of
% @variant actor-present
% @lean Newspeak.PrologBridge.PrologActorInstancesOf.present
% @mode actor_instances_of(+,+,+,-)
actor_instances_of(World, Class, [Actor | Remaining], Values) :-
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, Heap),
    heap_all_instances(
        heap_all_instances(Heap, Class, Current), Heap, Class, Current),
    actor_instances_of(World, Class, Remaining, Later),
    list_append(Current, Later, Values).

% @latex equation:all-instances-of
% @variant cohort
% @lean Newspeak.PrologBridge.PrologAllCohortInstancesOf.enumerate
% @mode all_instances_of(+,+,-)
all_instances_of(World, Class, Values) :-
    actor_world_field(World, value_heap, SharedHeap),
    heap_all_instances(
        heap_all_instances(SharedHeap, Class, Shared),
        SharedHeap, Class, Shared),
    actor_world_field(World, actor_allocations, store(ActorEntries)),
    store_entry_keys(ActorEntries, Actors),
    actor_instances_of(World, Class, Actors, ActorValues),
    list_append(Shared, ActorValues, Values).

% @latex equation:mixin-applications
% @variant heap-application
% @lean Newspeak.PrologBridge.PrologHeapAllApplications.application
% @mode heap_all_applications(+,+,+,-)
heap_all_applications(
    heap_all_applications(Heap, Mixin, Classes), Heap, Mixin, Classes).

% @latex equation:mixin-applications
% @variant locate-empty
% @lean Newspeak.PrologBridge.PrologLocateClasses.empty
% @mode locate_classes(+,+,-)
locate_classes(_Location, [], []).

% @latex equation:mixin-applications
% @variant locate-step
% @lean Newspeak.PrologBridge.PrologLocateClasses.step
% @mode locate_classes(+,+,-)
locate_classes(Location, [Class | Remaining],
               [located_class(Location, Class) | Located]) :-
    locate_classes(Location, Remaining, Located).

% @latex equation:mixin-applications
% @variant actor-empty
% @lean Newspeak.PrologBridge.PrologActorApplicationsOf.empty
% @mode actor_applications_of(+,+,+,-)
actor_applications_of(_World, _Mixin, [], []).

% @latex equation:mixin-applications
% @variant actor-absent
% @lean Newspeak.PrologBridge.PrologActorApplicationsOf.absent
% @mode actor_applications_of(+,+,+,-)
actor_applications_of(World, Mixin, [Actor | Remaining], Values) :-
    actor_allocation(World, Actor, none),
    actor_applications_of(World, Mixin, Remaining, Values).

% @latex equation:mixin-applications
% @variant actor-present
% @lean Newspeak.PrologBridge.PrologActorApplicationsOf.present
% @mode actor_applications_of(+,+,+,-)
actor_applications_of(World, Mixin, [Actor | Remaining], Values) :-
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, Heap),
    heap_all_applications(
        heap_all_applications(Heap, Mixin, Classes), Heap, Mixin, Classes),
    locate_classes(actor_heap(Actor), Classes, Current),
    actor_applications_of(World, Mixin, Remaining, Later),
    list_append(Current, Later, Values).

% @latex equation:mixin-applications
% @variant cohort
% @lean Newspeak.PrologBridge.PrologAllCohortApplicationsOf.enumerate
% @mode mixin_applications(+,+,-)
mixin_applications(World, Mixin, Values) :-
    actor_world_field(World, value_heap, SharedHeap),
    heap_all_applications(
        heap_all_applications(SharedHeap, Mixin, Classes),
        SharedHeap, Mixin, Classes),
    locate_classes(shared_heap, Classes, Shared),
    actor_world_field(World, actor_allocations, store(ActorEntries)),
    store_entry_keys(ActorEntries, Actors),
    actor_applications_of(World, Mixin, Actors, ActorValues),
    list_append(Shared, ActorValues, Values).

% @latex equation:method-owner
% @variant mixin-methods
% @lean Newspeak.MixinDef.methods
% @mode mixin_methods(+,-)
mixin_methods(
    mixin_def(_Declaration, Methods, _OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, _InitializerSelector,
              _InitializerParameters, _InitializerGroups,
              _InitializerBody),
    Methods).

% @latex equation:method-owner
% @variant in-mixin-empty
% @lean Newspeak.PrologBridge.PrologFindMethodInMixin.empty
% @mode find_method_in_mixin(+,+,+,-)
find_method_in_mixin(_Mixin, _Method, [], none).

% @latex equation:method-owner
% @variant in-mixin-hit
% @lean Newspeak.PrologBridge.PrologFindMethodInMixin.hit
% @mode find_method_in_mixin(+,+,+,-)
find_method_in_mixin(Mixin, Method, [Selector | _Remaining],
                     some(Definition)) :-
    mixin_methods(Mixin, Methods),
    store_lookup(Methods, Selector, some(Definition)),
    method_identity(Definition, Method).

% @latex equation:method-owner
% @variant in-mixin-different
% @lean Newspeak.PrologBridge.PrologFindMethodInMixin.different
% @mode find_method_in_mixin(+,+,+,-)
find_method_in_mixin(Mixin, Method, [Selector | Remaining], Result) :-
    mixin_methods(Mixin, Methods),
    store_lookup(Methods, Selector, some(Definition)),
    method_identity(Definition, Other),
    dif(Other, Method),
    find_method_in_mixin(Mixin, Method, Remaining, Result).

% @latex equation:method-owner
% @variant in-mixin-absent
% @lean Newspeak.PrologBridge.PrologFindMethodInMixin.absent
% @mode find_method_in_mixin(+,+,+,-)
find_method_in_mixin(Mixin, Method, [Selector | Remaining], Result) :-
    mixin_methods(Mixin, Methods),
    store_lookup(Methods, Selector, none),
    find_method_in_mixin(Mixin, Method, Remaining, Result).

% @latex equation:method-owner
% @variant definition-empty
% @lean Newspeak.PrologBridge.PrologFindMethodDefinition.empty
% @mode find_method_definition(+,+,+,-)
find_method_definition(_Program, _Method, [], none).

% @latex equation:method-owner
% @variant definition-hit
% @lean Newspeak.PrologBridge.PrologFindMethodDefinition.hit
% @mode find_method_definition(+,+,+,-)
find_method_definition(Program, Method, [MixinId | _Remaining],
                       some(pair(MixinId, Definition))) :-
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, some(Mixin)),
    mixin_methods(Mixin, Methods),
    store_entry_keys(Methods, Selectors),
    find_method_in_mixin(Mixin, Method, Selectors, some(Definition)).

% @latex equation:method-owner
% @variant definition-no-method
% @lean Newspeak.PrologBridge.PrologFindMethodDefinition.noMethod
% @mode find_method_definition(+,+,+,-)
find_method_definition(Program, Method, [MixinId | Remaining], Result) :-
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, some(Mixin)),
    mixin_methods(Mixin, Methods),
    store_entry_keys(Methods, Selectors),
    find_method_in_mixin(Mixin, Method, Selectors, none),
    find_method_definition(Program, Method, Remaining, Result).

% @latex equation:method-owner
% @variant definition-no-mixin
% @lean Newspeak.PrologBridge.PrologFindMethodDefinition.noMixin
% @mode find_method_definition(+,+,+,-)
find_method_definition(Program, Method, [MixinId | Remaining], Result) :-
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, none),
    find_method_definition(Program, Method, Remaining, Result).

% @latex equation:method-owner
% @variant owner
% @lean Newspeak.PrologBridge.PrologMethodOwner.owner
% @mode program_method_owner(+,+,-)
program_method_owner(Program, Method, Mixin) :-
    program_mixins(Program, Mixins),
    store_entry_keys(Mixins, MixinIds),
    find_method_definition(
        Program, Method, MixinIds, some(pair(Mixin, _Definition))).

% @latex equation:method-formals
% @lean Newspeak.PrologBridge.PrologMethodFormals.formals
% @mode program_method_formals(+,+,-)
program_method_formals(Program, Method, Formals) :-
    program_mixins(Program, Mixins),
    store_entry_keys(Mixins, MixinIds),
    find_method_definition(
        Program, Method, MixinIds, some(pair(_Mixin, Definition))),
    method_parameters(Definition, Formals).

% @latex equation:live-activation-order
% @variant stack-empty
% @lean Newspeak.PrologBridge.PrologActivationIds.empty
% @mode activation_stack_ids(+,-)
activation_stack_ids(activation_stack_empty, []).

% @latex equation:live-activation-order
% @variant stack-push
% @lean Newspeak.PrologBridge.PrologActivationIds.push
% @mode activation_stack_ids(+,-)
activation_stack_ids(
    activation_stack_push(Rest, activation_frame(Activation, _Frames)), Ids) :-
    activation_stack_ids(Rest, RestIds),
    list_append(RestIds, [Activation], Ids).

% @latex equation:live-activation-order
% @variant state-idle
% @lean Newspeak.PrologBridge.PrologRunStateActivationIds.idle
% @mode run_state_activation_ids(+,-)
run_state_activation_ids(idle, []).

% @latex equation:live-activation-order
% @variant state-running
% @lean Newspeak.PrologBridge.PrologRunStateActivationIds.running
% @mode run_state_activation_ids(+,-)
run_state_activation_ids(
    running_turn(sequential_config(_Allocation, Stack, _Control),
                 _Reply, _Event), Ids) :-
    activation_stack_ids(Stack, Ids).

% @latex equation:live-activation-order
% @variant state-paused
% @lean Newspeak.PrologBridge.PrologRunStateActivationIds.paused
% @mode run_state_activation_ids(+,-)
run_state_activation_ids(
    paused_turn(sequential_config(_Allocation, Stack, _Control),
                _Reply, _Event, _Token, _Reason), Ids) :-
    activation_stack_ids(Stack, Ids).

% @latex equation:live-activation-order
% @variant actors-empty
% @lean Newspeak.PrologBridge.PrologLiveActivationIdsFrom.empty
% @mode live_activation_ids_from(+,+,-)
live_activation_ids_from(_World, [], []).

% @latex equation:live-activation-order
% @variant actor-absent
% @lean Newspeak.PrologBridge.PrologLiveActivationIdsFrom.absent
% @mode live_activation_ids_from(+,+,-)
live_activation_ids_from(World, [Actor | Remaining], Ids) :-
    actor_run_state(World, Actor, none),
    live_activation_ids_from(World, Remaining, Later),
    list_deduplicated(Later, Ids).

% @latex equation:live-activation-order
% @variant actor-present
% @lean Newspeak.PrologBridge.PrologLiveActivationIdsFrom.present
% @mode live_activation_ids_from(+,+,-)
live_activation_ids_from(World, [Actor | Remaining], Ids) :-
    actor_run_state(World, Actor, some(State)),
    run_state_activation_ids(State, Current),
    live_activation_ids_from(World, Remaining, Later),
    list_append(Current, Later, Combined),
    list_deduplicated(Combined, Ids).

% @latex equation:live-activation-order
% @variant live-set
% @lean Newspeak.ActorWorld.liveActivationIds
% @mode live_activation_ids(+,-)
live_activation_ids(World, Ids) :-
    actor_world_field(World, run_states, store(Entries)),
    store_entry_keys(Entries, Actors),
    live_activation_ids_from(World, Actors, Ids).

% @latex equation:live-activation-order
% @variant before-here
% @lean Newspeak.PrologBridge.PrologListBefore.here
% @mode list_before(+,+,+)
list_before(First, Second, [First | Remaining]) :-
    list_member(Second, Remaining).

% @latex equation:live-activation-order
% @variant before-later
% @lean Newspeak.PrologBridge.PrologListBefore.later
% @mode list_before(+,+,+)
list_before(First, Second, [_Head | Remaining]) :-
    list_before(First, Second, Remaining).

% @latex equation:live-activation-order
% @variant actor-below
% @lean Newspeak.PrologBridge.PrologActorBelow.below
% @mode actor_activation_below(+,+,+,+)
actor_activation_below(World, Actor, Lower, Upper) :-
    actor_run_state(World, Actor, some(State)),
    run_state_activation_ids(State, Ids),
    list_before(Lower, Upper, Ids).

% Reflection-command fields are deliberately constructor-by-constructor: the
% clauses are the auditable partition behind requiredRight and commandTarget.

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-method-body
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(replace_method_body(Mirror, Method, _Body),
                          Mirror, method_target(Method), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-method-definition
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_method_definition(
        Mirror, _Mixin, Method, _Definition, _Locals, _Body),
    Mirror, method_target(Method), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant add-method-definition
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    add_method_definition(Mirror, Mixin, _Definition, _Locals, _Body),
    Mirror, mixin_target(Mixin), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant remove-method-definition
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    remove_method_definition(Mirror, _Mixin, Method),
    Mirror, method_target(Method), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-slot-declarations
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_slot_declarations(Mirror, Mixin, _Groups),
    Mirror, mixin_target(Mixin), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-nested-declarations
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_nested_declarations(Mirror, Mixin, _Declarations),
    Mirror, mixin_target(Mixin), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-mixin-initializer
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_mixin_initializer(Mirror, Mixin, _Initializer),
    Mirror, mixin_target(Mixin), edit_code).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant change-superclass
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(change_superclass(Mirror, Class, _Superclass),
                          Mirror, class_target(Class), edit_class).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant change-class-enclosing-object
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    change_class_enclosing_object(Mirror, Class, _Object),
    Mirror, class_target(Class), edit_class).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant change-object-class
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(change_object_class(Mirror, Object, _Class),
                          Mirror, object_target(ordinary_object(Object)),
                          reclassify_object).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant object-slot-write
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(object_slot_write(Mirror, Object, _Slot, _Value),
                          Mirror, object_target(ordinary_object(Object)),
                          edit_object_slots).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant activation-parameter-write
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    activation_parameter_write(Mirror, Activation, _Parameter, _Value),
    Mirror, activation_target(Activation), edit_activation).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant activation-local-write
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    activation_local_write(Mirror, Activation, _Slot, _Value),
    Mirror, activation_target(Activation), edit_activation).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant change-activation-current-class
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    change_activation_current_class(Mirror, Activation, _Class),
    Mirror, activation_target(Activation), edit_activation).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant change-activation-continuation
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    change_activation_continuation(Mirror, Activation, _Continuation),
    Mirror, activation_target(Activation), edit_activation).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant make-activation-uncontinuable
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    make_activation_uncontinuable(Mirror, Activation),
    Mirror, activation_target(Activation), edit_activation).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant continue-at-activation
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    continue_at_activation(Mirror, _Actor, Activation, _Value),
    Mirror, activation_target(Activation), control_continuation).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant pause-actor
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(pause_actor(Mirror, Actor, _Reason),
                          Mirror, actor_target(Actor), control_actor_stack).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-current-actor-stack
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_current_actor_stack(Mirror, Actor, _Stack),
    Mirror, actor_target(Actor), control_actor_stack).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-paused-actor-stack
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_paused_actor_stack(Mirror, Actor, _Token, _Stack),
    Mirror, actor_target(Actor), control_actor_stack).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant resume-paused-actor-full-speed
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    resume_paused_actor_at_full_speed(Mirror, Actor, _Token),
    Mirror, actor_target(Actor), control_actor_stack).

% @latex equation:reflection-command-right
% @also equation:reflection-command-target
% @variant replace-and-resume-paused-actor-stack
% @lean Newspeak.PrologBridge.PrologReflectionCommandFields
% @mode reflection_command_fields(+,-,-,-)
reflection_command_fields(
    replace_and_resume_paused_actor_stack(
        Mirror, Actor, _Token, _Stack),
    Mirror, actor_target(Actor), control_actor_stack).

% @latex equation:reflection-authorized
% @lean Newspeak.PrologBridge.PrologReflectionCommandAuthorized.authorize
% @mode reflection_command_authorized(+,+,+)
reflection_command_authorized(World, Actor, Command) :-
    reflection_command_fields(Command, Mirror, Target, Right),
    mirror_authorizes(
        mirror_authorizes(World, Actor, Mirror, Target, Right),
        World, Actor, Mirror, Target, Right).

% @latex equation:reflection-command-footprint
% @variant replace-method-body
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(replace_method_body(_Mirror, Method, _Body),
                          [method_body_location(Method)]).

% @latex equation:reflection-command-footprint
% @variant replace-method-definition
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_method_definition(
        _Mirror, Mixin, Method, Definition, _Locals, _Body),
    [method_definition_location(Method), method_body_location(Method),
     method_dictionary_location(Mixin), selector_location(Mixin, Selector)]) :-
    method_selector(Definition, Selector).

% @latex equation:reflection-command-footprint
% @variant add-method-definition
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    add_method_definition(_Mirror, Mixin, Definition, _Locals, _Body),
    [method_definition_location(Method), method_body_location(Method),
     method_dictionary_location(Mixin), selector_location(Mixin, Selector)]) :-
    method_identity(Definition, Method),
    method_selector(Definition, Selector).

% @latex equation:reflection-command-footprint
% @variant remove-method-definition
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    remove_method_definition(_Mirror, Mixin, Method),
    [method_definition_location(Method), method_body_location(Method),
     method_dictionary_location(Mixin)]).

% @latex equation:reflection-command-footprint
% @variant replace-slots
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_slot_declarations(_Mirror, Mixin, _Groups),
    [slot_declarations_location(Mixin)]).

% @latex equation:reflection-command-footprint
% @variant replace-nested
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_nested_declarations(_Mirror, Mixin, _Declarations),
    [nested_declarations_location(Mixin)]).

% @latex equation:reflection-command-footprint
% @variant replace-initializer
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_mixin_initializer(_Mirror, Mixin, _Initializer),
    [mixin_initializer_location(Mixin)]).

% @latex equation:reflection-command-footprint
% @variant superclass
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(change_superclass(_Mirror, Class, _Superclass),
                          [superclass_location(Class)]).

% @latex equation:reflection-command-footprint
% @variant class-enclosing
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    change_class_enclosing_object(_Mirror, Class, _Object),
    [class_enclosing_object_location(Class)]).

% @latex equation:reflection-command-footprint
% @variant object-class
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(change_object_class(_Mirror, Object, _Class),
                          [object_class_location(Object)]).

% @latex equation:reflection-command-footprint
% @variant object-slot
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(object_slot_write(_Mirror, Object, Slot, _Value),
                          [object_slot_location(Object, Slot)]).

% @latex equation:reflection-command-footprint
% @variant activation-parameter
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    activation_parameter_write(_Mirror, Activation, Parameter, _Value),
    [activation_field_location(Activation, parameter_field(Parameter))]).

% @latex equation:reflection-command-footprint
% @variant activation-local
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    activation_local_write(_Mirror, Activation, Slot, _Value),
    [activation_field_location(Activation, local_field(Slot))]).

% @latex equation:reflection-command-footprint
% @variant activation-class
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    change_activation_current_class(_Mirror, Activation, _Class),
    [activation_field_location(Activation, current_class_field)]).

% @latex equation:reflection-command-footprint
% @variant activation-continuation
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    change_activation_continuation(_Mirror, Activation, _Continuation),
    [activation_field_location(Activation, continuation_field)]).

% @latex equation:reflection-command-footprint
% @variant activation-uncontinuable
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    make_activation_uncontinuable(_Mirror, Activation),
    [activation_graph_location,
     activation_field_location(Activation, continuable_field)]).

% @latex equation:reflection-command-footprint
% @variant continuation-transfer
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    continue_at_activation(_Mirror, Actor, Activation, _Value),
    [actor_stack_location(Actor), activation_graph_location,
     activation_field_location(Activation, continuation_field)]).

% @latex equation:reflection-command-footprint
% @variant pause
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(pause_actor(_Mirror, Actor, _Reason),
                          [actor_stack_location(Actor),
                           pause_token_supply_location]).

% @latex equation:reflection-command-footprint
% @variant replace-current-stack
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_current_actor_stack(_Mirror, Actor, Stack),
    [actor_stack_location(Actor), activation_graph_location | Locations]) :-
    stack_template_record_locations(Stack, Locations).

% @latex equation:reflection-command-footprint
% @variant replace-paused-stack
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_paused_actor_stack(_Mirror, Actor, _Token, Stack),
    [pause_token_supply_location, actor_stack_location(Actor),
     activation_graph_location | Locations]) :-
    stack_template_record_locations(Stack, Locations).

% @latex equation:reflection-command-footprint
% @variant resume-paused
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    resume_paused_actor_at_full_speed(_Mirror, Actor, _Token),
    [actor_stack_location(Actor)]).

% @latex equation:reflection-command-footprint
% @variant replace-and-resume-paused
% @lean Newspeak.PrologBridge.PrologReflectionCommandWrites
% @mode reflection_command_writes(+,-)
reflection_command_writes(
    replace_and_resume_paused_actor_stack(_Mirror, Actor, _Token, Stack),
    [actor_stack_location(Actor), activation_graph_location | Locations]) :-
    stack_template_record_locations(Stack, Locations).

% @latex equation:reflection-location-overlap
% @variant same
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.same
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(Location, Location).

% @latex equation:reflection-location-overlap
% @variant record-field
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.recordField
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    activation_record_location(Activation),
    activation_field_location(Activation, Field)).

% @latex equation:reflection-location-overlap
% @variant field-record
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.fieldRecord
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    activation_field_location(Activation, Field),
    activation_record_location(Activation)).

% @latex equation:reflection-location-overlap
% @variant dictionary-selector
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.dictionarySelector
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    method_dictionary_location(Mixin), selector_location(Mixin, Selector)).

% @latex equation:reflection-location-overlap
% @variant selector-dictionary
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.selectorDictionary
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    selector_location(Mixin, Selector), method_dictionary_location(Mixin)).

% @latex equation:reflection-location-overlap
% @variant graph-record
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.graphRecord
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    activation_graph_location, activation_record_location(Activation)).

% @latex equation:reflection-location-overlap
% @variant record-graph
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.recordGraph
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    activation_record_location(Activation), activation_graph_location).

% @latex equation:reflection-location-overlap
% @variant graph-field
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.graphField
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    activation_graph_location,
    activation_field_location(Activation, Field)).

% @latex equation:reflection-location-overlap
% @variant field-graph
% @lean Newspeak.PrologBridge.PrologReflectionLocationsOverlap.fieldGraph
% @mode reflection_locations_overlap(+,+)
reflection_locations_overlap(
    activation_field_location(Activation, Field),
    activation_graph_location).

% @latex equation:reflection-conflict
% @variant natural-less-zero-successor
% @lean Newspeak.PrologBridge.PrologNaturalStrictLess.zero
% @mode natural_strict_less(+,+)
natural_strict_less(zero, succ(_Right)).

% @latex equation:reflection-conflict
% @variant natural-less-successor
% @lean Newspeak.PrologBridge.PrologNaturalStrictLess.successor
% @mode natural_strict_less(+,+)
natural_strict_less(succ(Left), succ(Right)) :-
    natural_strict_less(Left, Right).

% @latex equation:reflection-conflict
% @variant one-based-head
% @lean Newspeak.PrologBridge.PrologListNthOneBased.head
% @mode list_nth_one_based(+,+,-)
list_nth_one_based([Element | _Remaining], succ(zero), Element).

% @latex equation:reflection-conflict
% @variant one-based-tail
% @lean Newspeak.PrologBridge.PrologListNthOneBased.tail
% @mode list_nth_one_based(+,+,-)
list_nth_one_based([_Element | Remaining], succ(succ(Index)), Result) :-
    list_nth_one_based(Remaining, succ(Index), Result).

% @latex equation:reflection-conflict
% @variant command-conflict
% @lean Newspeak.PrologBridge.PrologReflectionCommandConflict.conflict
% @mode reflection_command_conflict(+,+)
reflection_command_conflict(First, Second) :-
    reflection_command_writes(First, FirstWrites),
    list_member(Left, FirstWrites),
    reflection_command_writes(Second, SecondWrites),
    list_member(Right, SecondWrites),
    reflection_locations_overlap(Left, Right).

% @latex equation:reflection-conflict
% @variant indexed-conflict
% @lean Newspeak.PrologBridge.PrologReflectionConflictAt.conflict
% @mode reflection_conflict(+,+,+)
reflection_conflict(Transaction, FirstIndex, SecondIndex) :-
    natural_strict_less(FirstIndex, SecondIndex),
    list_nth_one_based(Transaction, FirstIndex, First),
    list_nth_one_based(Transaction, SecondIndex, Second),
    reflection_command_conflict(First, Second).

% Nonconflict is the universal negative complement and is therefore carried
% as an explicit proof object rather than implemented by negation-as-failure.
% @latex equation:reflection-conflict
% @variant nonconflicting-witness
% @lean Newspeak.PrologBridge.PrologReflectionTransactionNonconflicting.witness
% @mode reflection_transaction_nonconflicting(+,+)
reflection_transaction_nonconflicting(
    reflection_transaction_nonconflicting(Transaction), Transaction).

% The seven command partitions share one structural list filter.
% @latex equation:reflection-command-right
% @variant family-code
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(edit_code, code_family).

% @latex equation:reflection-command-right
% @variant family-class
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(edit_class, class_graph_family).

% @latex equation:reflection-command-right
% @variant family-object-class
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(reclassify_object, object_class_family).

% @latex equation:reflection-command-right
% @variant family-object-slot
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(edit_object_slots, object_slot_family).

% @latex equation:reflection-command-right
% @variant family-activation
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(edit_activation, activation_family).

% @latex equation:reflection-command-right
% @variant family-continuation
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(control_continuation, continuation_family).

% @latex equation:reflection-command-right
% @variant family-debugger
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_right_family(+,-)
reflection_right_family(control_actor_stack, debugger_family).

% @latex equation:reflection-command-right
% @variant command-family
% @lean Newspeak.PrologBridge.PrologReflectionCommandFamily.classified
% @mode reflection_command_family(+,-)
reflection_command_family(Command, Family) :-
    reflection_command_fields(Command, _Mirror, _Target, Right),
    reflection_right_family(Right, Family).

% @latex equation:code-command-projection
% @also equation:class-command-projections
% @also equation:control-command-projections
% @also equation:debugger-command-projection
% @variant filter-empty
% @lean Newspeak.PrologBridge.PrologFilterReflectionCommands.empty
% @mode filter_reflection_commands(+,+,-)
filter_reflection_commands(_Family, [], []).

% @latex equation:code-command-projection
% @also equation:class-command-projections
% @also equation:control-command-projections
% @also equation:debugger-command-projection
% @variant filter-keep
% @lean Newspeak.PrologBridge.PrologFilterReflectionCommands.keep
% @mode filter_reflection_commands(+,+,-)
filter_reflection_commands(
    Family, [Command | Remaining], [Command | Filtered]) :-
    reflection_command_family(Command, Family),
    filter_reflection_commands(Family, Remaining, Filtered).

% @latex equation:code-command-projection
% @also equation:class-command-projections
% @also equation:control-command-projections
% @also equation:debugger-command-projection
% @variant filter-skip
% @lean Newspeak.PrologBridge.PrologFilterReflectionCommands.skip
% @mode filter_reflection_commands(+,+,-)
filter_reflection_commands(Family, [Command | Remaining], Filtered) :-
    reflection_command_family(Command, Actual),
    dif(Actual, Family),
    filter_reflection_commands(Family, Remaining, Filtered).

% @latex equation:code-command-projection
% @lean Newspeak.codeCommands
% @mode reflection_code_commands(+,-)
reflection_code_commands(Commands, Filtered) :-
    filter_reflection_commands(code_family, Commands, Filtered).

% @latex equation:class-command-projections
% @variant class-graph
% @lean Newspeak.classGraphCommands
% @mode reflection_class_commands(+,-)
reflection_class_commands(Commands, Filtered) :-
    filter_reflection_commands(class_graph_family, Commands, Filtered).

% @latex equation:class-command-projections
% @variant object-class
% @lean Newspeak.objectClassCommands
% @mode reflection_object_class_commands(+,-)
reflection_object_class_commands(Commands, Filtered) :-
    filter_reflection_commands(object_class_family, Commands, Filtered).

% @latex equation:class-command-projections
% @variant object-slot
% @lean Newspeak.objectSlotCommands
% @mode reflection_object_slot_commands(+,-)
reflection_object_slot_commands(Commands, Filtered) :-
    filter_reflection_commands(object_slot_family, Commands, Filtered).

% @latex equation:control-command-projections
% @variant activation
% @lean Newspeak.activationCommands
% @mode reflection_activation_commands(+,-)
reflection_activation_commands(Commands, Filtered) :-
    filter_reflection_commands(activation_family, Commands, Filtered).

% @latex equation:control-command-projections
% @variant continuation
% @lean Newspeak.continuationCommands
% @mode reflection_continuation_commands(+,-)
reflection_continuation_commands(Commands, Filtered) :-
    filter_reflection_commands(continuation_family, Commands, Filtered).

% @latex equation:debugger-command-projection
% @lean Newspeak.debuggerCommands
% @mode reflection_debugger_commands(+,-)
reflection_debugger_commands(Commands, Filtered) :-
    filter_reflection_commands(debugger_family, Commands, Filtered).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.actorAllocations
% @mode actor_allocation(+,+,-)
actor_allocation(World, Actor, Result) :-
    actor_world_field(World, actor_allocations, Allocations),
    store_lookup(Allocations, Actor, Result).

% @latex equation:actor-heap-view
% @variant view
% @lean Newspeak.PrologBridge.PrologActorHeapView
% @mode actor_heap_view(+,+,-,-)
actor_heap_view(World, Actor, SharedHeap, PrivateHeap) :-
    actor_world_field(World, value_heap, SharedHeap),
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, PrivateHeap).

% The two universal disjointness obligations are proof-carrying invariants.
% @latex equation:actor-heap-view
% @variant private-disjoint
% @lean Newspeak.PrologBridge.PrologPrivateHeapsDisjoint.witness
% @mode private_heaps_disjoint(+,+)
private_heaps_disjoint(private_heaps_disjoint(World), World).

% @latex equation:actor-heap-view
% @variant shared-disjoint
% @lean Newspeak.PrologBridge.PrologValueHeapDisjoint.witness
% @mode value_heap_disjoint(+,+)
value_heap_disjoint(value_heap_disjoint(World), World).

% @latex equation:actor-configuration
% @variant mailbox-present
% @lean Newspeak.ActorWorld.mailbox
% @mode actor_mailbox(+,+,-)
actor_mailbox(World, Actor, Mailbox) :-
    actor_world_field(World, mailboxes, Mailboxes),
    store_lookup(Mailboxes, Actor, some(Mailbox)).

% @latex equation:actor-configuration
% @variant mailbox-absent
% @lean Newspeak.ActorWorld.mailbox
% @mode actor_mailbox(+,+,-)
actor_mailbox(World, Actor, []) :-
    actor_world_field(World, mailboxes, Mailboxes),
    store_lookup(Mailboxes, Actor, none).

% @latex equation:actor-configuration
% @variant history-present
% @lean Newspeak.ActorWorld.causalHistory
% @mode actor_causal_history(+,+,-)
actor_causal_history(World, Actor, History) :-
    actor_world_field(World, histories, Histories),
    store_lookup(Histories, Actor, some(History)).

% @latex equation:actor-configuration
% @variant history-absent
% @lean Newspeak.ActorWorld.causalHistory
% @mode actor_causal_history(+,+,-)
actor_causal_history(World, Actor, []) :-
    actor_world_field(World, histories, Histories),
    store_lookup(Histories, Actor, none).

% @latex equation:actor-configuration
% @lean Newspeak.ActorPacket.identity
% @mode actor_packet_identity(+,-)
actor_packet_identity(
    actor_packet(Identity, _Source, _Destination, _History, _Payload),
    Identity).

% @latex equation:actor-configuration
% @lean Newspeak.ActorPacket.causalHistory
% @mode actor_packet_causal_history(+,-)
actor_packet_causal_history(
    actor_packet(_Identity, _Source, _Destination, History, _Payload),
    History).

% @latex equation:actor-configuration
% @lean Newspeak.ActorPacket.payload
% @mode actor_packet_payload(+,-)
actor_packet_payload(
    actor_packet(_Identity, _Source, _Destination, _History, Payload),
    Payload).

% @latex equation:actor-configuration
% @variant deduplicate-empty
% @lean Newspeak.FiniteStore.deduplicated
% @mode list_deduplicated(+,-)
list_deduplicated([], []).

% @latex equation:actor-configuration
% @variant deduplicate-present
% @lean Newspeak.FiniteStore.deduplicated
% @mode list_deduplicated(+,-)
list_deduplicated([Element|Remaining], Result) :-
    list_deduplicated(Remaining, Result),
    list_member(Element, Result).

% @latex equation:actor-configuration
% @variant deduplicate-absent
% @lean Newspeak.FiniteStore.deduplicated
% @mode list_deduplicated(+,-)
list_deduplicated([Element|Remaining], [Element|Result]) :-
    list_deduplicated(Remaining, Result),
    list_not_member(Element, Result).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.mergeEventSets
% @mode merge_event_sets(+,+,-)
merge_event_sets(Left, Right, Result) :-
    list_append(Left, Right, Combined),
    list_deduplicated(Combined, Result).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.addEventToSet
% @mode add_event_to_set(+,+,-)
add_event_to_set(History, Event, Result) :-
    list_append(History, [Event], Extended),
    list_deduplicated(Extended, Result).

% --------------------------------------------------------------------------
% Modules and top-level entry
% --------------------------------------------------------------------------

% @latex equation:module-definition
% @variant class-origin
% @lean Newspeak.ClassDef.origin
% @mode class_origin(+,-)
class_origin(
    class_def(_Mixin, _Superclass, _EnclosingObject, _Metaclass,
              Origin, _Factory),
    Origin).

% @latex equation:module-definition
% @lean Newspeak.Program.ModuleDefinition
% @mode module_definition(+,+,+)
module_definition(Program, Heap, Class) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(Definition)),
    class_primary_factory(Definition, some(_Factory)),
    class_origin(Definition, expression(named_class(Declaration))),
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(top_owner)).

% @latex equation:module-instance
% @lean Newspeak.Program.ModuleInstance
% @mode module_instance(+,+,+)
module_instance(Program, Heap, Object) :-
    class_of(Heap, Object, some(Class)),
    module_definition(Program, Heap, Class).

% @latex equation:top-level-expression
% @variant atom
% @lean Newspeak.Program.TopLevelExpression.atom
% @mode top_level_expression(+,+)
top_level_expression(_Program, atom(_Payload)).

% @latex equation:top-level-expression
% @variant closure
% @lean Newspeak.Program.TopLevelExpression.closure
% @mode top_level_expression(+,+)
top_level_expression(_Program, closure_literal(_Declaration)).

% @latex equation:top-level-expression
% @variant tuple
% @lean Newspeak.Program.TopLevelExpression.tuple
% @mode top_level_expression(+,+)
top_level_expression(Program, tuple(_Site, _Descriptor, Elements)) :-
    top_level_expression_list(Program, Elements).

% @latex equation:top-level-expression
% @variant object-literal
% @lean Newspeak.Program.TopLevelExpression.objectLiteral
% @mode top_level_expression(+,+)
top_level_expression(Program, object_literal(Declaration, _Superclass)) :-
    program_object_literal_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(top_owner)).

% @latex equation:top-level-expression
% @variant class-body
% @lean Newspeak.Program.TopLevelExpression.classBody
% @mode top_level_expression(+,+)
top_level_expression(Program, class_body(Declaration, _Superclass)) :-
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(top_owner)).

% @latex equation:top-level-expression
% @variant mixin-application
% @lean Newspeak.Program.TopLevelExpression.mixinApply
% @mode top_level_expression(+,+)
top_level_expression(
    Program, mixin_apply(Declaration, _Superclass, _MixinSource)) :-
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(top_owner)).

% @latex equation:top-level-expression
% @variant ordinary-send
% @lean Newspeak.Program.TopLevelExpression.ordinarySend
% @mode top_level_expression(+,+)
top_level_expression(Program, ordinary_send(Receiver, _Selector, Arguments)) :-
    top_level_expression(Program, Receiver),
    top_level_expression_list(Program, Arguments).

% @latex equation:top-level-expression
% @variant list-empty
% @lean Newspeak.PrologBridge.PrologTopLevelExpressionList
% @mode top_level_expression_list(+,+)
top_level_expression_list(_Program, []).

% @latex equation:top-level-expression
% @variant list-cons
% @lean Newspeak.PrologBridge.PrologTopLevelExpressionList
% @mode top_level_expression_list(+,+)
top_level_expression_list(Program, [Expression|Expressions]) :-
    top_level_expression(Program, Expression),
    top_level_expression_list(Program, Expressions).

% @latex equation:run-program
% @lean Newspeak.Program.TopLevelEntry.run
% @mode run_program(+,+,+,-)
run_program(
    Program, State, Expression,
    sequential_config(
        NewState,
        activation_stack_push(
            activation_stack_empty,
            activation_frame(TopActivation, eval_stack_empty)),
        evaluate(Expression))) :-
    top_level_expression(Program, Expression),
    allocate_top_level_activation(
        Program, State, NewState, TopActivation).

% @latex equation:application-object
% @lean Newspeak.Program.ApplicationObject
% @mode application_object(+,+,+)
application_object(Program, Heap, Object) :-
    class_of(Heap, Object, some(Class)),
    public_lookup(
        Program, Heap, selector('main:args:'), Class,
        some(lookup_result(Method, _DefiningClass))),
    method_parameters(Method, Parameters),
    list_length(Parameters, succ(succ(zero))).

% @latex equation:new-top-activation
% @lean Newspeak.Program.topLevelActivationDefinition
% @mode top_level_activation_definition(+,-)
top_level_activation_definition(
    Program,
    activation_def(
        ActivationClass, top_provenance, store([]), store([]), NilObject,
        none, none, none, true, store([]), store([]))) :-
    activation_class(Program, ActivationClass),
    program_nil_object(Program, NilObject).

% @latex equation:new-top-activation
% @lean Newspeak.Program.allocateTopLevelActivation
% @mode allocate_top_level_activation(+,+,-,-)
allocate_top_level_activation(
    Program,
    allocation_state(
        Heap, NextMirror, NextActivation, NextClosure, NextObject, NextClass),
    allocation_state(
        NewHeap, NextMirror, succ(NextActivation), NextClosure, NextObject,
        NextClass),
    activation_id(NextActivation)) :-
    top_level_activation_definition(Program, Definition),
    heap_install_activation(
        Heap, activation_id(NextActivation), Definition, NewHeap).

% @latex equation:application-entry
% @lean Newspeak.Program.applicationTurnConfiguration
% @mode application_turn_configuration(+,+,+,+,-)
application_turn_configuration(
    Program, State, Receiver, Message,
    sequential_config(
        NewState,
        activation_stack_push(
            activation_stack_empty,
            activation_frame(TopActivation, eval_stack_empty)),
        dispatch(ordinary_request(Receiver), Message))) :-
    allocate_top_level_activation(
        Program, State, NewState, TopActivation).

% `local_message_materialization/5` is the proof-carrying application graph of
% the platform boundary that turns eventual handles into ordinary local
% Newspeak objects.  It is intentionally not implemented by the language.
% @latex equation:application-entry
% @variant materialization-witness
% @lean Newspeak.LocalMessageMaterialization
% @mode local_message_materialization(+,+,+,+,-)
local_message_materialization(
    materialization(World, Actor, EventualMessage, Message),
    World, Actor, EventualMessage, Message).

% @latex rule:Turn-Start
% @variant update
% @lean Newspeak.ActorWorld.startApplicationTurn
% @mode start_application_turn(+,+,+,+,+,+,+,+,-)
start_application_turn(
    World, Actor, State, Packet, Remaining, Receiver, Message, ReplyPromise,
    FinalWorld) :-
    actor_world_program(World, Program),
    application_turn_configuration(
        Program, State, Receiver, Message,
        sequential_config(NewAllocation, Stack, Control)),
    actor_causal_history(World, Actor, CurrentHistory),
    actor_packet_causal_history(Packet, PacketHistory),
    merge_event_sets(CurrentHistory, PacketHistory, MergedHistory),
    actor_packet_identity(Packet, PacketIdentity),
    add_event_to_set(MergedHistory, PacketIdentity, NewHistory),
    actor_world_field(World, actor_allocations, Allocations),
    store_install(Allocations, Actor, NewAllocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, WithAllocation),
    actor_world_field(WithAllocation, run_states, RunStates),
    store_install(
        RunStates, Actor,
        running_turn(
            sequential_config(NewAllocation, Stack, Control),
            ReplyPromise, PacketIdentity),
        NewRunStates),
    actor_world_install_field(
        WithAllocation, run_states, NewRunStates, WithRunState),
    actor_world_field(WithRunState, mailboxes, Mailboxes),
    store_install(Mailboxes, Actor, Remaining, NewMailboxes),
    actor_world_install_field(
        WithRunState, mailboxes, NewMailboxes, WithMailbox),
    actor_world_field(WithMailbox, histories, Histories),
    store_install(Histories, Actor, NewHistory, NewHistories),
    actor_world_install_field(
        WithMailbox, histories, NewHistories, FinalWorld).

% @latex rule:Turn-Start
% @lean Newspeak.ActorTurnStartStep.application
% @mode actor_turn_start_step(+,+,+,-)
actor_turn_start_step(Materialization, Actor, World, After) :-
    actor_run_state(World, Actor, some(idle)),
    actor_mailbox(World, Actor, [Packet|Remaining]),
    actor_allocation(World, Actor, some(State)),
    actor_packet_payload(
        Packet,
        application_payload(Receiver, EventualMessage, ReplyPromise)),
    local_message_materialization(
        Materialization, World, Actor, EventualMessage, Message),
    start_application_turn(
        World, Actor, State, Packet, Remaining, Receiver, Message,
        ReplyPromise, After).

% The three witnesses below are positive proof objects for propositions that
% are premises of Actor-Sequential but are not executable data transforms.

% @latex equation:configuration
% @variant allocation-projection
% @lean Newspeak.SequentialConfig.allocation
% @mode sequential_config_allocation(+,-)
sequential_config_allocation(
    sequential_config(Allocation, _Stack, _Control), Allocation).

% @latex rule:Actor-Sequential
% @variant well-formed-witness
% @lean Newspeak.Program.WellFormed
% @mode actor_heap_well_formed(+,+,+)
actor_heap_well_formed(
    actor_heap_well_formed(Program, Heap), Program, Heap).

% @latex rule:Actor-Sequential
% @variant nonterminal-witness
% @lean Newspeak.SequentialConfig.TurnTerminal
% @mode non_turn_terminal(+,+)
non_turn_terminal(non_turn_terminal(Configuration), Configuration).

% @latex rule:Actor-Sequential
% @variant non-eventual-witness
% @lean Newspeak.SequentialConfig.EventualDispatch
% @mode non_eventual_dispatch(+,+)
non_eventual_dispatch(non_eventual_dispatch(Configuration), Configuration).

% @latex rule:Actor-Sequential
% @variant advance-running-turn
% @lean Newspeak.ActorWorld.advanceRunningTurn
% @mode advance_running_turn(+,+,+,+,+,-)
advance_running_turn(
    World, Actor, AfterConfiguration, ReplyPromise, TriggeringEvent,
    FinalWorld) :-
    actor_world_field(World, actor_allocations, Allocations),
    sequential_config_allocation(
        AfterConfiguration, AfterConfigurationAllocation),
    store_install(
        Allocations, Actor, AfterConfigurationAllocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, WithAllocation),
    actor_world_field(WithAllocation, run_states, RunStates),
    store_install(
        RunStates, Actor,
        running_turn(AfterConfiguration, ReplyPromise, TriggeringEvent),
        NewRunStates),
    actor_world_install_field(
        WithAllocation, run_states, NewRunStates, FinalWorld).

% @latex rule:Actor-Sequential
% @lean Newspeak.ActorSequentialStep.advance
% @mode actor_sequential_step(+,+,+,+,+,+,+,-)
actor_sequential_step(
    Program, Reification, WellFormedWitness, NonterminalWitness,
    NonEventualWitness, Actor, World, AfterWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(Before, ReplyPromise, TriggeringEvent))),
    sequential_config_allocation(Before, Allocation),
    actor_allocation(World, Actor, some(Allocation)),
    actor_world_program(World, Program),
    allocation_state_heap(Allocation, Heap),
    actor_heap_well_formed(WellFormedWitness, Program, Heap),
    non_turn_terminal(NonterminalWitness, Before),
    non_eventual_dispatch(NonEventualWitness, Before),
    sequential_step_with_top_level(
        Program, Reification, Before, After),
    advance_running_turn(
        World, Actor, After, ReplyPromise, TriggeringEvent, AfterWorld).

% --------------------------------------------------------------------------
% Actor capabilities, remote representation, and eventual routing
% --------------------------------------------------------------------------

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.promises
% @mode actor_promise(+,+,-)
actor_promise(World, Promise, Result) :-
    actor_world_field(World, promises, Promises),
    store_lookup(Promises, Promise, Result).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.farReferences
% @mode actor_far_reference(+,+,-)
actor_far_reference(World, Identity, Result) :-
    actor_world_field(World, far_references, FarReferences),
    store_lookup(FarReferences, Identity, Result).

% These three clauses are application witnesses for the two platform
% predicates in the actor semantics and the negative branch of `isValue`.
% @latex rule:RR-Value
% @variant value-witness
% @lean Newspeak.RemoteRepresentation.value
% @mode actor_is_value(+,+,+,+)
actor_is_value(is_value(World, Actor, Object), World, Actor, Object).

% @latex rule:RR-Near-Far
% @variant nonvalue-witness
% @lean Newspeak.RemoteRepresentation.nearFar
% @mode actor_is_not_value(+,+,+,+)
actor_is_not_value(not_value(World, Actor, Object), World, Actor, Object).

% @latex rule:RR-Value
% @variant transfer-witness
% @lean Newspeak.ValueTransferRelation
% @mode actor_value_transfer(+,+,+,+,+,-,-)
actor_value_transfer(
    value_transfer(World, Source, Destination, Object, After, Represented),
    World, Source, Destination, Object, After, Represented).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.ownsNearReference
% @mode actor_owns_near_reference(+,+,+,+)
actor_owns_near_reference(
    owns_near_reference(World, Actor, Object), World, Actor, Object).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.installNextFarReference
% @mode install_next_far_reference(+,+,+,-,-)
install_next_far_reference(
    World, Actor, Object, FinalWorld, far_reference_id(NextFarReference)) :-
    actor_world_field(World, next_far_reference, NextFarReference),
    actor_world_field(World, far_references, FarReferences),
    store_install(
        FarReferences, far_reference_id(NextFarReference),
        far_reference_target(Actor, Object), NewFarReferences),
    actor_world_install_field(
        World, far_references, NewFarReferences, WithReference),
    actor_world_install_field(
        WithReference, next_far_reference, succ(NextFarReference), FinalWorld).

% @latex rule:RR-Same
% @lean Newspeak.RemoteRepresentation.same
% @mode remote_representation(+,+,+,+,+,+,-,-)
remote_representation(
    _IsValue, _ValueTransfer, World, Source, Source, Reference,
    World, Reference).

% @latex rule:RR-Value
% @lean Newspeak.RemoteRepresentation.value
% @mode remote_representation(+,+,+,+,+,+,-,-)
remote_representation(
    IsValue, ValueTransfer, World, Source, Destination,
    near_reference(Object), After, near_reference(Represented)) :-
    dif(Source, Destination),
    actor_is_value(IsValue, World, Source, Object),
    actor_value_transfer(
        ValueTransfer, World, Source, Destination, Object, After,
        Represented).

% @latex rule:RR-Far-Home
% @lean Newspeak.RemoteRepresentation.farHome
% @mode remote_representation(+,+,+,+,+,+,-,-)
remote_representation(
    _IsValue, _ValueTransfer, World, Source, Destination,
    far_reference(Identity), World, near_reference(Object)) :-
    dif(Source, Destination),
    actor_far_reference(
        World, Identity,
        some(far_reference_target(Destination, Object))).

% @latex rule:RR-Far-Pass
% @lean Newspeak.RemoteRepresentation.farPass
% @mode remote_representation(+,+,+,+,+,+,-,-)
remote_representation(
    _IsValue, _ValueTransfer, World, Source, Destination,
    far_reference(Identity), World, far_reference(Identity)) :-
    dif(Source, Destination),
    actor_far_reference(
        World, Identity,
        some(far_reference_target(TargetActor, _Object))),
    dif(TargetActor, Destination).

% @latex rule:RR-Promise
% @lean Newspeak.RemoteRepresentation.promise
% @mode remote_representation(+,+,+,+,+,+,-,-)
remote_representation(
    _IsValue, _ValueTransfer, World, Source, Destination,
    promise_reference(Identity), World, promise_reference(Identity)) :-
    dif(Source, Destination),
    actor_promise(World, Identity, some(_State)).

% @latex rule:RR-Near-Far
% @lean Newspeak.RemoteRepresentation.nearFar
% @mode remote_representation(+,+,+,+,+,+,-,-)
remote_representation(
    IsNotValue, _ValueTransfer, World, Source, Destination,
    near_reference(Object), After, far_reference(Identity)) :-
    dif(Source, Destination),
    actor_owns_near_reference(
        owns_near_reference(World, Source, Object), World, Source, Object),
    actor_is_not_value(IsNotValue, World, Source, Object),
    install_next_far_reference(
        World, Source, Object, After, Identity).

% @latex equation:message-transfer
% @variant arguments-empty
% @lean Newspeak.RemoteArgumentListRepresentation.nil
% @mode remote_argument_list_representation(+,+,+,+,+,+,-,-)
remote_argument_list_representation(
    _IsValue, _ValueTransfer, Source, Destination, World, [], World, []).

% @latex equation:message-transfer
% @variant arguments-cons
% @lean Newspeak.RemoteArgumentListRepresentation.cons
% @mode remote_argument_list_representation(+,+,+,+,+,+,-,-)
remote_argument_list_representation(
    IsValue, ValueTransfer, Source, Destination, World,
    [Argument|Arguments], After, [Represented|RepresentedArguments]) :-
    remote_representation(
        IsValue, ValueTransfer, World, Source, Destination, Argument,
        Middle, Represented),
    remote_argument_list_representation(
        IsValue, ValueTransfer, Source, Destination, Middle, Arguments,
        After, RepresentedArguments).

% @latex equation:message-transfer
% @lean Newspeak.RemoteMessageRepresentation.message
% @mode remote_message_representation(+,+,+,+,+,+,-,-)
remote_message_representation(
    IsValue, ValueTransfer, Source, Destination, World,
    eventual_message(Selector, Arguments), After,
    eventual_message(Selector, RepresentedArguments)) :-
    remote_argument_list_representation(
        IsValue, ValueTransfer, Source, Destination, World, Arguments,
        After, RepresentedArguments).

% Packet emission is split at the local/cross-actor branch of Equation (10.8).
% @latex equation:emit-packet
% @variant local
% @lean Newspeak.ActorWorld.emitPacket
% @mode emit_actor_packet(+,+,+,+,-)
emit_actor_packet(World, Actor, Actor, Payload, FinalWorld) :-
    actor_world_field(World, next_event, NextEvent),
    actor_causal_history(World, Actor, History),
    make_actor_packet(
        event_id(NextEvent), Actor, Actor, History, Payload, Packet),
    actor_world_field(World, event_ledger, EventLedger),
    store_install(
        EventLedger, event_id(NextEvent),
        event_record(Actor, Actor, History), NewEventLedger),
    add_event_to_set(History, event_id(NextEvent), NewHistory),
    actor_world_field(World, histories, Histories),
    store_install(Histories, Actor, NewHistory, NewHistories),
    actor_mailbox(World, Actor, Mailbox),
    list_append(Mailbox, [Packet], NewMailbox),
    actor_world_field(World, mailboxes, Mailboxes),
    store_install(Mailboxes, Actor, NewMailbox, NewMailboxes),
    actor_world_field(World, delivered_events, DeliveredEvents),
    actor_world_delivered_to(World, Actor, Delivered),
    list_append(Delivered, [event_id(NextEvent)], NewDelivered),
    store_install(DeliveredEvents, Actor, NewDelivered, NewDeliveredEvents),
    actor_world_install_field(
        World, event_ledger, NewEventLedger, WithLedger),
    actor_world_install_field(
        WithLedger, histories, NewHistories, WithHistory),
    actor_world_install_field(
        WithHistory, mailboxes, NewMailboxes, WithMailbox),
    actor_world_install_field(
        WithMailbox, delivered_events, NewDeliveredEvents, WithDelivery),
    actor_world_install_field(
        WithDelivery, next_event, succ(NextEvent), FinalWorld).

% @latex equation:emit-packet
% @variant remote
% @lean Newspeak.ActorWorld.emitPacket
% @mode emit_actor_packet(+,+,+,+,-)
emit_actor_packet(World, Source, Destination, Payload, FinalWorld) :-
    dif(Source, Destination),
    actor_world_field(World, next_event, NextEvent),
    actor_causal_history(World, Source, History),
    make_actor_packet(
        event_id(NextEvent), Source, Destination, History, Payload, Packet),
    actor_world_field(World, event_ledger, EventLedger),
    store_install(
        EventLedger, event_id(NextEvent),
        event_record(Source, Destination, History), NewEventLedger),
    add_event_to_set(History, event_id(NextEvent), NewHistory),
    actor_world_field(World, histories, Histories),
    store_install(Histories, Source, NewHistory, NewHistories),
    actor_world_field(World, network, Network),
    list_append(Network, [Packet], NewNetwork),
    actor_world_install_field(
        World, event_ledger, NewEventLedger, WithLedger),
    actor_world_install_field(
        WithLedger, histories, NewHistories, WithHistory),
    actor_world_install_field(
        WithHistory, network, NewNetwork, WithNetwork),
    actor_world_install_field(
        WithNetwork, next_event, succ(NextEvent), FinalWorld).

% @latex equation:emit-packet
% @variant packet-constructor
% @lean Newspeak.ActorPacket
% @mode make_actor_packet(+,+,+,+,+,-)
make_actor_packet(
    Identity, Source, Destination, History, Payload,
    actor_packet(Identity, Source, Destination, History, Payload)).

% @latex equation:actor-configuration
% @variant delivered-present
% @lean Newspeak.ActorWorld.deliveredTo
% @mode actor_world_delivered_to(+,+,-)
actor_world_delivered_to(World, Actor, Delivered) :-
    actor_world_field(World, delivered_events, DeliveredEvents),
    store_lookup(DeliveredEvents, Actor, some(Delivered)).

% @latex equation:actor-configuration
% @variant delivered-absent
% @lean Newspeak.ActorWorld.deliveredTo
% @mode actor_world_delivered_to(+,+,-)
actor_world_delivered_to(World, Actor, []) :-
    actor_world_field(World, delivered_events, DeliveredEvents),
    store_lookup(DeliveredEvents, Actor, none).

% @latex equation:event-ledger
% @variant record
% @lean Newspeak.ActorWorld.eventLedger
% @mode actor_event_record(+,+,-)
actor_event_record(World, Event, Result) :-
    actor_world_field(World, event_ledger, Ledger),
    store_lookup(Ledger, Event, Result).

% @latex equation:event-ledger
% @variant destination
% @lean Newspeak.EventRecord.destination
% @mode actor_event_destination(+,+,-)
actor_event_destination(World, Event, Destination) :-
    actor_event_record(
        World, Event,
        some(event_record(_Source, Destination, _History))).

% @latex equation:event-ledger
% @variant delivered-sequence
% @lean Newspeak.ActorWorld.deliveredTo
% @mode actor_delivered_sequence(+,+,-)
actor_delivered_sequence(World, Actor, Delivered) :-
    actor_world_delivered_to(World, Actor, Delivered).

% @latex rule:Async-Return
% @variant allocate-pending
% @lean Newspeak.ActorWorld.allocatePendingPromise
% @mode allocate_pending_promise(+,+,-,-)
allocate_pending_promise(
    World, Owner, FinalWorld, promise_id(NextPromise)) :-
    actor_world_field(World, next_promise, NextPromise),
    actor_world_field(World, promises, Promises),
    store_install(
        Promises, promise_id(NextPromise), pending_promise(Owner, []),
        NewPromises),
    actor_world_install_field(World, promises, NewPromises, WithPromise),
    actor_world_install_field(
        WithPromise, next_promise, succ(NextPromise), FinalWorld).

% @latex rule:Route-Pending
% @variant register-waiter
% @lean Newspeak.ActorWorld.registerPromiseWaiter
% @mode register_promise_waiter(+,+,+,+,+,-)
register_promise_waiter(
    World, Promise, Owner, Waiters, Waiter, FinalWorld) :-
    list_append(Waiters, [Waiter], NewWaiters),
    actor_world_field(World, promises, Promises),
    store_install(
        Promises, Promise, pending_promise(Owner, NewWaiters), NewPromises),
    actor_world_install_field(World, promises, NewPromises, FinalWorld).

% @latex rule:Route-Target
% @also equation:eventual-target
% @variant near-private
% @lean Newspeak.EventualTarget.nearPrivate
% @mode eventual_target(+,+,+,-,-)
eventual_target(
    World, Current, near_reference(Object), Current, Object) :-
    actor_owns_near_reference(
        owns_near_reference(World, Current, Object), World, Current, Object).

% @latex rule:Route-Target
% @also equation:eventual-target
% @variant near-shared
% @lean Newspeak.EventualTarget.nearShared
% @mode eventual_target(+,+,+,-,-)
eventual_target(
    World, Current, near_reference(Object), Current, Object) :-
    actor_shared_live_object(
        shared_live_object(World, Object), World, Object).

% @latex rule:Route-Target
% @variant shared-live-witness
% @lean Newspeak.EventualTarget.nearShared
% @mode actor_shared_live_object(+,+,+)
actor_shared_live_object(
    shared_live_object(World, Object), World, Object).

% @latex rule:Route-Target
% @also equation:eventual-target
% @variant far
% @lean Newspeak.EventualTarget.far
% @mode eventual_target(+,+,+,-,-)
eventual_target(
    World, _Current, far_reference(Identity), TargetActor, Object) :-
    actor_far_reference(
        World, Identity,
        some(far_reference_target(TargetActor, Object))).

% @latex equation:wake-all
% @variant empty
% @lean Newspeak.ActorWorld.wakeAllWaiters
% @mode wake_all_waiters(+,+,+,+,+,+,-)
wake_all_waiters(
    World, _Owner, _SettledPromise, _Disposition, _Result, [], World).

% @latex equation:wake-all
% @variant cons
% @lean Newspeak.ActorWorld.wakeAllWaiters
% @mode wake_all_waiters(+,+,+,+,+,+,-)
wake_all_waiters(
    World, Owner, SettledPromise, Disposition, Result,
    [promise_waiter(Actor, Message, ResultPromise, WaiterHistory)|Remaining],
    After) :-
    emit_actor_packet(
        World, Owner, Actor,
        wake_payload(
            SettledPromise, ResultPromise, Disposition, Result, Message,
            WaiterHistory),
        Emitted),
    wake_all_waiters(
        Emitted, Owner, SettledPromise, Disposition, Result, Remaining, After).

% @latex equation:promise-settlement
% @variant commit-fulfilled
% @lean Newspeak.commitPromiseSettlement
% @mode commit_promise_settlement(+,+,+,+,+,+,-)
commit_promise_settlement(
    World, Promise, Owner, fulfilled, Represented, Waiters, After) :-
    actor_world_field(World, promises, Promises),
    store_install(
        Promises, Promise, fulfilled_promise(Owner, Represented), NewPromises),
    actor_world_install_field(World, promises, NewPromises, Committed),
    wake_all_waiters(
        Committed, Owner, Promise, fulfilled, Represented, Waiters, After).

% @latex equation:promise-settlement
% @variant commit-broken
% @lean Newspeak.commitPromiseSettlement
% @mode commit_promise_settlement(+,+,+,+,+,+,-)
commit_promise_settlement(
    World, Promise, Owner, broken, Represented, Waiters, After) :-
    actor_world_field(World, promises, Promises),
    store_install(
        Promises, Promise, broken_promise(Owner, Represented), NewPromises),
    actor_world_install_field(World, promises, NewPromises, Committed),
    wake_all_waiters(
        Committed, Owner, Promise, broken, Represented, Waiters, After).

% @latex equation:promise-settlement
% @variant history-subset-empty
% @lean List.Subset
% @mode list_subset(+,+)
list_subset([], _Superset).

% @latex equation:promise-settlement
% @variant history-subset-cons
% @lean List.Subset
% @mode list_subset(+,+)
list_subset([Element|Remaining], Superset) :-
    list_member(Element, Superset),
    list_subset(Remaining, Superset).

% @latex equation:promise-settlement
% @lean Newspeak.PromiseSettlement.settle
% @mode promise_settlement(+,+,+,+,+,+,+,+,-)
promise_settlement(
    IsValue, ValueTransfer, World, Promise, Disposition, Source, Result,
    History, After) :-
    actor_promise(World, Promise, some(pending_promise(Owner, Waiters))),
    actor_causal_history(World, Owner, OwnerHistory),
    list_subset(History, OwnerHistory),
    remote_representation(
        IsValue, ValueTransfer, World, Source, Owner, Result,
        RepresentedWorld, Represented),
    commit_promise_settlement(
        RepresentedWorld, Promise, Owner, Disposition, Represented, Waiters,
        After).

% @latex rule:Route-Target
% @lean Newspeak.RouteEventualMessage.target
% @mode route_eventual_message(+,+,+,+,+,+,+,+,-)
route_eventual_message(
    IsValue, ValueTransfer, World, Requester, Receiver, Message,
    ResultPromise, _History, After) :-
    eventual_target(
        World, Requester, Receiver, TargetActor, TargetObject),
    remote_message_representation(
        IsValue, ValueTransfer, Requester, TargetActor, World, Message,
        RepresentedWorld, RepresentedMessage),
    emit_actor_packet(
        RepresentedWorld, Requester, TargetActor,
        application_payload(
            TargetObject, RepresentedMessage, ResultPromise),
        After).

% @latex rule:Route-Pending
% @lean Newspeak.RouteEventualMessage.pending
% @mode route_eventual_message(+,+,+,+,+,+,+,+,-)
route_eventual_message(
    _IsValue, _ValueTransfer, World, Requester,
    promise_reference(Promise), Message, ResultPromise, History, After) :-
    actor_promise(World, Promise, some(pending_promise(Owner, Waiters))),
    register_promise_waiter(
        World, Promise, Owner, Waiters,
        promise_waiter(Requester, Message, ResultPromise, History), After).

% @latex rule:Route-Fulfilled
% @lean Newspeak.RouteEventualMessage.fulfilled
% @mode route_eventual_message(+,+,+,+,+,+,+,+,-)
route_eventual_message(
    IsValue, ValueTransfer, World, Requester,
    promise_reference(Promise), Message, ResultPromise, History, After) :-
    actor_promise(World, Promise, some(fulfilled_promise(Owner, Result))),
    remote_representation(
        IsValue, ValueTransfer, World, Owner, Requester, Result,
        RepresentedWorld, Represented),
    route_eventual_message(
        IsValue, ValueTransfer, RepresentedWorld, Requester, Represented,
        Message, ResultPromise, History, After).

% @latex rule:Route-Broken
% @lean Newspeak.RouteEventualMessage.broken
% @mode route_eventual_message(+,+,+,+,+,+,+,+,-)
route_eventual_message(
    IsValue, ValueTransfer, World, Requester,
    promise_reference(Promise), Message, ResultPromise, History, After) :-
    actor_promise(World, Promise, some(broken_promise(Owner, Exception))),
    remote_representation(
        IsValue, ValueTransfer, World, Owner, Requester, Exception,
        RepresentedWorld, Represented),
    promise_settlement(
        IsValue, ValueTransfer, RepresentedWorld, ResultPromise, broken,
        Requester, Represented, History, After).

% @latex rule:Async-Return
% @variant asynchronous-send
% @lean Newspeak.AsynchronousSend.send
% @mode asynchronous_send(+,+,+,+,+,+,+,-,-)
asynchronous_send(
    IsValue, ValueTransfer, World, Actor, Receiver, Message, History,
    After, ResultPromise) :-
    allocate_pending_promise(World, Actor, Allocated, ResultPromise),
    route_eventual_message(
        IsValue, ValueTransfer, Allocated, Actor, Receiver, Message,
        ResultPromise, History, After).

% The remaining three application graphs are platform boundaries used by
% Async-Return.  Concrete platforms supply the witnesses.
% @latex rule:Async-Return
% @variant reference-interpretation-witness
% @lean Newspeak.LocalEventualReferenceInterpretation
% @mode local_eventual_reference_interpretation(+,+,+,+,-)
local_eventual_reference_interpretation(
    reference_interpretation(World, Actor, Object, Reference),
    World, Actor, Object, Reference).

% @latex rule:Async-Return
% @variant message-interpretation-witness
% @lean Newspeak.LocalEventualMessageInterpretation
% @mode local_eventual_message_interpretation(+,+,+,+,-)
local_eventual_message_interpretation(
    message_interpretation(World, Actor, Message, EventualMessage),
    World, Actor, Message, EventualMessage).

% @latex rule:Async-Return
% @variant promise-handle-witness
% @lean Newspeak.PromiseHandleInstallation
% @mode promise_handle_installation(+,+,+,+,+,-,-)
promise_handle_installation(
    promise_handle(
        World, Actor, Before, Promise, After, PromiseObject),
    World, Actor, Before, Promise, After, PromiseObject).

% @latex rule:Async-Return
% @lean Newspeak.ActorEventualSendStep.send
% @mode actor_eventual_send_step(+,+,+,+,+,+,+,+,+,+,-)
actor_eventual_send_step(
    ReferenceInterpretation, MessageInterpretation, HandleInstallation,
    IsValue, ValueTransfer, Actor, World, ReplyPromise, TriggeringEvent,
    Configuration, AfterWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(Configuration, ReplyPromise, TriggeringEvent))),
    sequential_config_allocation(Configuration, Allocation),
    actor_allocation(World, Actor, some(Allocation)),
    eventual_dispatch_configuration(
        Configuration, Allocation, ReceiverObject, Message),
    local_eventual_reference_interpretation(
        ReferenceInterpretation, World, Actor, ReceiverObject, Receiver),
    local_eventual_message_interpretation(
        MessageInterpretation, World, Actor, Message, EventualMessage),
    actor_causal_history(World, Actor, History),
    asynchronous_send(
        IsValue, ValueTransfer, World, Actor, Receiver, EventualMessage,
        History, Routed, ResultPromise),
    promise_handle_installation(
        HandleInstallation, Routed, Actor, Allocation, ResultPromise,
        ResultAllocation, PromiseObject),
    return_eventual_promise(
        Configuration, ResultAllocation, PromiseObject,
        ResultConfiguration),
    advance_running_turn(
        Routed, Actor, ResultConfiguration, ReplyPromise, TriggeringEvent,
        AfterWorld).

% @latex rule:Async-Return
% @variant eventual-configuration
% @lean Newspeak.ControlTerm.dispatch
% @mode eventual_dispatch_configuration(+,+,-,-)
eventual_dispatch_configuration(
    sequential_config(
        Allocation, _Stack,
        dispatch(eventual_request(ReceiverObject), Message)),
    Allocation, ReceiverObject, Message).

% @latex rule:Async-Return
% @variant return-promise
% @lean Newspeak.SequentialConfig.returnEventualPromise
% @mode return_eventual_promise(+,+,+,-)
return_eventual_promise(
    sequential_config(_OldAllocation, Stack, _OldControl),
    Allocation, Handle,
    sequential_config(Allocation, Stack, object(Handle))).

% --------------------------------------------------------------------------
% Actor completion, system packets, and network delivery
% --------------------------------------------------------------------------

% @latex equation:packet-grammar
% @lean Newspeak.ActorPacket.source
% @mode actor_packet_source(+,-)
actor_packet_source(
    actor_packet(_Identity, Source, _Destination, _History, _Payload), Source).

% @latex equation:actor-configuration
% @lean Newspeak.ActorWorld.consumeHeadPacket
% @mode consume_head_packet(+,+,+,+,+,-)
consume_head_packet(
    World, Actor, Packet, Remaining, AdditionalHistory, FinalWorld) :-
    actor_causal_history(World, Actor, CurrentHistory),
    actor_packet_causal_history(Packet, PacketHistory),
    merge_event_sets(CurrentHistory, PacketHistory, FirstMerge),
    merge_event_sets(FirstMerge, AdditionalHistory, SecondMerge),
    actor_packet_identity(Packet, Identity),
    add_event_to_set(SecondMerge, Identity, NewHistory),
    actor_world_field(World, mailboxes, Mailboxes),
    store_install(Mailboxes, Actor, Remaining, NewMailboxes),
    actor_world_install_field(World, mailboxes, NewMailboxes, WithMailbox),
    actor_world_field(WithMailbox, histories, Histories),
    store_install(Histories, Actor, NewHistory, NewHistories),
    actor_world_install_field(
        WithMailbox, histories, NewHistories, FinalWorld).

% @latex rule:Turn-Fulfill-Local
% @variant finish-running-turn
% @lean Newspeak.ActorWorld.finishRunningTurn
% @mode finish_running_turn(+,+,+,-)
finish_running_turn(World, Actor, Allocation, FinalWorld) :-
    actor_world_field(World, actor_allocations, Allocations),
    store_install(Allocations, Actor, Allocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, WithAllocation),
    actor_world_field(WithAllocation, run_states, RunStates),
    store_install(RunStates, Actor, idle, NewRunStates),
    actor_world_install_field(
        WithAllocation, run_states, NewRunStates, FinalWorld).

% @latex rule:Turn-Fulfill-Local
% @lean Newspeak.ActorTurnCompletionStep.local
% @mode actor_turn_completion_step(+,+,+,+,+,-)
actor_turn_completion_step(
    IsValue, ValueTransfer, Actor, World, fulfilled, FinalWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(
            sequential_config(Allocation, activation_stack_empty,
                              halt_control(Value)),
            ReplyPromise, _TriggeringEvent))),
    actor_promise(
        World, ReplyPromise, some(pending_promise(Actor, _Waiters))),
    actor_causal_history(World, Actor, History),
    promise_settlement(
        IsValue, ValueTransfer, World, ReplyPromise, fulfilled, Actor,
        near_reference(Value), History, Settled),
    finish_running_turn(Settled, Actor, Allocation, FinalWorld).

% @latex rule:Turn-Break-Local
% @lean Newspeak.ActorTurnCompletionStep.local
% @mode actor_turn_completion_step(+,+,+,+,+,-)
actor_turn_completion_step(
    IsValue, ValueTransfer, Actor, World, broken, FinalWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(
            sequential_config(Allocation, activation_stack_empty,
                              abort(Exception)),
            ReplyPromise, _TriggeringEvent))),
    actor_promise(
        World, ReplyPromise, some(pending_promise(Actor, _Waiters))),
    actor_causal_history(World, Actor, History),
    promise_settlement(
        IsValue, ValueTransfer, World, ReplyPromise, broken, Actor,
        near_reference(Exception), History, Settled),
    finish_running_turn(Settled, Actor, Allocation, FinalWorld).

% @latex rule:Turn-Fulfill-Remote
% @lean Newspeak.ActorTurnCompletionStep.remote
% @mode actor_turn_completion_step(+,+,+,+,+,-)
actor_turn_completion_step(
    _IsValue, _ValueTransfer, Actor, World, fulfilled, FinalWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(
            sequential_config(Allocation, activation_stack_empty,
                              halt_control(Value)),
            ReplyPromise, _TriggeringEvent))),
    actor_promise(
        World, ReplyPromise, some(pending_promise(Owner, _Waiters))),
    dif(Owner, Actor),
    emit_actor_packet(
        World, Actor, Owner,
        settlement_payload(
            ReplyPromise, fulfilled, near_reference(Value)),
        Emitted),
    finish_running_turn(Emitted, Actor, Allocation, FinalWorld).

% @latex rule:Turn-Break-Remote
% @lean Newspeak.ActorTurnCompletionStep.remote
% @mode actor_turn_completion_step(+,+,+,+,+,-)
actor_turn_completion_step(
    _IsValue, _ValueTransfer, Actor, World, broken, FinalWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(
            sequential_config(Allocation, activation_stack_empty,
                              abort(Exception)),
            ReplyPromise, _TriggeringEvent))),
    actor_promise(
        World, ReplyPromise, some(pending_promise(Owner, _Waiters))),
    dif(Owner, Actor),
    emit_actor_packet(
        World, Actor, Owner,
        settlement_payload(
            ReplyPromise, broken, near_reference(Exception)),
        Emitted),
    finish_running_turn(Emitted, Actor, Allocation, FinalWorld).

% @latex rule:Settlement-Packet-Dequeue
% @lean Newspeak.SettlementPacketDequeueStep.dequeue
% @mode settlement_packet_dequeue_step(+,+,+,+,-)
settlement_packet_dequeue_step(
    IsValue, ValueTransfer, Actor, World, After) :-
    actor_run_state(World, Actor, some(idle)),
    actor_mailbox(World, Actor, [Packet|Remaining]),
    actor_packet_payload(
        Packet,
        settlement_payload(Promise, Disposition, Result)),
    consume_head_packet(
        World, Actor, Packet, Remaining, [], Consumed),
    actor_packet_source(Packet, Source),
    actor_causal_history(Consumed, Actor, History),
    promise_settlement(
        IsValue, ValueTransfer, Consumed, Promise, Disposition, Source,
        Result, History, After).

% @latex rule:Wake-Fulfilled
% @lean Newspeak.WakePacketDequeueStep.fulfilled
% @mode wake_packet_dequeue_step(+,+,+,+,+,-)
wake_packet_dequeue_step(
    IsValue, ValueTransfer, Actor, World, fulfilled, After) :-
    actor_run_state(World, Actor, some(idle)),
    actor_mailbox(World, Actor, [Packet|Remaining]),
    actor_packet_payload(
        Packet,
        wake_payload(
            _SettledPromise, ResultPromise, fulfilled, Result, Message,
            WaiterHistory)),
    consume_head_packet(
        World, Actor, Packet, Remaining, WaiterHistory, Consumed),
    actor_packet_source(Packet, Source),
    remote_representation(
        IsValue, ValueTransfer, Consumed, Source, Actor, Result,
        RepresentedWorld, Represented),
    actor_causal_history(RepresentedWorld, Actor, History),
    route_eventual_message(
        IsValue, ValueTransfer, RepresentedWorld, Actor, Represented, Message,
        ResultPromise, History, After).

% @latex rule:Wake-Broken
% @lean Newspeak.WakePacketDequeueStep.broken
% @mode wake_packet_dequeue_step(+,+,+,+,+,-)
wake_packet_dequeue_step(
    IsValue, ValueTransfer, Actor, World, broken, After) :-
    actor_run_state(World, Actor, some(idle)),
    actor_mailbox(World, Actor, [Packet|Remaining]),
    actor_packet_payload(
        Packet,
        wake_payload(
            _SettledPromise, ResultPromise, broken, Result, _Message,
            WaiterHistory)),
    consume_head_packet(
        World, Actor, Packet, Remaining, WaiterHistory, Consumed),
    actor_packet_source(Packet, Source),
    actor_causal_history(Consumed, Actor, History),
    promise_settlement(
        IsValue, ValueTransfer, Consumed, ResultPromise, broken, Source,
        Result, History, After).

% Positive witness for the universal E-order eligibility premise.
% @latex equation:e-order-eligibility
% @lean Newspeak.ActorWorld.PacketEligible
% @mode packet_eligible(+,+,+)
packet_eligible(packet_eligible(World, Packet), World, Packet).

% First-occurrence list erasure, matching `List.erase` on packet identity.
% @latex rule:Network-Deliver
% @variant erase-head
% @lean List.erase
% @mode list_erase_first(+,+,-)
list_erase_first(Element, [Element|Remaining], Remaining).

% @latex rule:Network-Deliver
% @variant erase-tail
% @lean List.erase
% @mode list_erase_first(+,+,-)
list_erase_first(Element, [Other|Remaining], [Other|Result]) :-
    dif(Element, Other),
    list_erase_first(Element, Remaining, Result).

% @latex rule:Network-Deliver
% @variant accept
% @lean Newspeak.ActorWorld.acceptNetworkPacket
% @mode accept_network_packet(+,+,-)
accept_network_packet(World, Packet, FinalWorld) :-
    actor_world_field(World, network, Network),
    list_erase_first(Packet, Network, NewNetwork),
    actor_packet_identity(Packet, Identity),
    actor_packet_destination(Packet, Destination),
    actor_mailbox(World, Destination, Mailbox),
    list_append(Mailbox, [Packet], NewMailbox),
    actor_world_field(World, mailboxes, Mailboxes),
    store_install(Mailboxes, Destination, NewMailbox, NewMailboxes),
    actor_world_delivered_to(World, Destination, Delivered),
    list_append(Delivered, [Identity], NewDelivered),
    actor_world_field(World, delivered_events, DeliveredEvents),
    store_install(
        DeliveredEvents, Destination, NewDelivered, NewDeliveredEvents),
    actor_world_install_field(World, network, NewNetwork, WithNetwork),
    actor_world_install_field(
        WithNetwork, mailboxes, NewMailboxes, WithMailbox),
    actor_world_install_field(
        WithMailbox, delivered_events, NewDeliveredEvents, FinalWorld).

% @latex equation:packet-grammar
% @lean Newspeak.ActorPacket.destination
% @mode actor_packet_destination(+,-)
actor_packet_destination(
    actor_packet(_Identity, _Source, Destination, _History, _Payload),
    Destination).

% --------------------------------------------------------------------------
% Actor creation
% --------------------------------------------------------------------------

% `actor_base_allocation/4` is the explicit graph parameter for the platform
% base-heap contract in Equation (10.23).
% @latex equation:create-actor
% @variant base-allocation-witness
% @lean Newspeak.ActorBaseAllocation
% @mode actor_base_allocation(+,+,+,+)
actor_base_allocation(
    actor_base_allocation(World, Actor, Base), World, Actor, Base).

% @latex equation:actor-seed
% @lean Newspeak.ActorSeedDescriptor
% @mode actor_seed_descriptor_fields(+,-,-,-,-,-,-)
actor_seed_descriptor_fields(
    actor_seed_descriptor(
        Declaration, ClassMixin, FactorySelector, FactoryParameters,
        InitializerDeclaration, SuperclassMessage),
    Declaration, ClassMixin, FactorySelector, FactoryParameters,
    InitializerDeclaration, SuperclassMessage).

% @latex equation:create-actor
% @variant seed-factory
% @lean Newspeak.actorSeedFactory
% @mode actor_seed_factory(+,-)
actor_seed_factory(
    Seed,
    factory_def(
        InitializerDeclaration, FactorySelector, FactoryParameters,
        body_initializer_plan(SuperclassMessage))) :-
    actor_seed_descriptor_fields(
        Seed, _Declaration, _ClassMixin, FactorySelector,
        FactoryParameters, InitializerDeclaration, SuperclassMessage).

% @latex equation:create-actor
% @lean Newspeak.ActorSpawn.spawn
% @mode spawn_actor(+,+,+,-)
spawn_actor(
    BaseWitness, World, InstanceMixin,
    actor_spawn_result(
        FinalWorld, actor_id(NextActor), ActorClass, FarReference)) :-
    actor_world_program(World, Program),
    program_field(Program, actor_seeds, ActorSeeds),
    store_lookup(ActorSeeds, InstanceMixin, some(Seed)),
    actor_seed_descriptor_fields(
        Seed, Declaration, ClassMixin, _FactorySelector,
        _FactoryParameters, _InitializerDeclaration, _SuperclassMessage),
    program_field(Program, decl_mixins, DeclMixins),
    store_lookup(
        DeclMixins, named_class(Declaration), some(InstanceMixin)),
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(top_owner)),
    actor_world_field(World, next_actor, NextActor),
    actor_base_allocation(
        BaseWitness, World, actor_id(NextActor), BaseAllocation),
    actor_seed_factory(Seed, Factory),
    object_class(Program, ObjectClass),
    program_nil_object(Program, NilObject),
    allocate_class_pair(
        Program, BaseAllocation, actor(named_class(Declaration)),
        InstanceMixin, ClassMixin, ObjectClass, NilObject, Factory,
        ActorAllocation, _ActorMetaclass, ActorClass),
    actor_world_field(World, actor_allocations, ActorAllocations),
    store_install(
        ActorAllocations, actor_id(NextActor), ActorAllocation,
        NewActorAllocations),
    actor_world_install_field(
        World, actor_allocations, NewActorAllocations, WithAllocation),
    actor_world_field(WithAllocation, run_states, RunStates),
    store_install(RunStates, actor_id(NextActor), idle, NewRunStates),
    actor_world_install_field(
        WithAllocation, run_states, NewRunStates, WithRunState),
    actor_world_field(WithRunState, mailboxes, Mailboxes),
    store_install(Mailboxes, actor_id(NextActor), [], NewMailboxes),
    actor_world_install_field(
        WithRunState, mailboxes, NewMailboxes, WithMailbox),
    actor_world_field(WithMailbox, histories, Histories),
    store_install(Histories, actor_id(NextActor), [], NewHistories),
    actor_world_install_field(
        WithMailbox, histories, NewHistories, WithHistory),
    actor_world_field(WithHistory, delivered_events, DeliveredEvents),
    store_install(
        DeliveredEvents, actor_id(NextActor), [], NewDeliveredEvents),
    actor_world_install_field(
        WithHistory, delivered_events, NewDeliveredEvents, WithDelivered),
    actor_world_install_field(
        WithDelivered, next_actor, succ(NextActor), Installed),
    install_next_far_reference(
        Installed, actor_id(NextActor), class_object(ActorClass),
        FinalWorld, FarReference).

% @latex rule:Network-Deliver
% @lean Newspeak.ActorNetworkDeliveryStep.deliver
% @mode actor_network_delivery_step(+,+,+,-)
actor_network_delivery_step(Eligibility, World, Packet, After) :-
    actor_world_field(World, network, Network),
    list_member(Packet, Network),
    packet_eligible(Eligibility, World, Packet),
    accept_network_packet(World, Packet, After).

% @latex equation:actor-configuration
% @variant selected-start
% @lean Newspeak.SelectedActorStep.start
% @mode selected_actor_step(+,+,+,+,+,+,+,+,+,+,-)
selected_actor_step(
    _Program, _Reification, Materialization, _ReferenceInterpretation,
    _MessageInterpretation, _HandleInstallation, _IsValue, _ValueTransfer,
    Actor, Before, After) :-
    actor_turn_start_step(Materialization, Actor, Before, After).

% @latex equation:actor-configuration
% @variant selected-sequential
% @lean Newspeak.SelectedActorStep.sequential
% @mode selected_actor_step(+,+,+,+,+,+,+,+,+,+,-)
selected_actor_step(
    Program, Reification, _Materialization, _ReferenceInterpretation,
    _MessageInterpretation, _HandleInstallation, _IsValue, _ValueTransfer,
    Actor, Before, After) :-
    actor_sequential_step(
        Program, Reification,
        actor_heap_well_formed(Program, _Heap),
        non_turn_terminal(_BeforeConfiguration),
        non_eventual_dispatch(_BeforeConfiguration),
        Actor, Before, After).

% @latex equation:actor-configuration
% @variant selected-eventual
% @lean Newspeak.SelectedActorStep.eventual
% @mode selected_actor_step(+,+,+,+,+,+,+,+,+,+,-)
selected_actor_step(
    _Program, _Reification, _Materialization, ReferenceInterpretation,
    MessageInterpretation, HandleInstallation, IsValue, ValueTransfer,
    Actor, Before, After) :-
    actor_run_state(
        Before, Actor,
        some(running_turn(Configuration, ReplyPromise, TriggeringEvent))),
    actor_eventual_send_step(
        ReferenceInterpretation, MessageInterpretation, HandleInstallation,
        IsValue, ValueTransfer, Actor, Before, ReplyPromise, TriggeringEvent,
        Configuration, After).

% @latex equation:actor-configuration
% @variant selected-complete
% @lean Newspeak.SelectedActorStep.complete
% @mode selected_actor_step(+,+,+,+,+,+,+,+,+,+,-)
selected_actor_step(
    _Program, _Reification, _Materialization, _ReferenceInterpretation,
    _MessageInterpretation, _HandleInstallation, IsValue, ValueTransfer,
    Actor, Before, After) :-
    actor_turn_completion_step(
        IsValue, ValueTransfer, Actor, Before, _Disposition, After).

% @latex equation:actor-configuration
% @variant selected-settlement
% @lean Newspeak.SelectedActorStep.settlement
% @mode selected_actor_step(+,+,+,+,+,+,+,+,+,+,-)
selected_actor_step(
    _Program, _Reification, _Materialization, _ReferenceInterpretation,
    _MessageInterpretation, _HandleInstallation, IsValue, ValueTransfer,
    Actor, Before, After) :-
    settlement_packet_dequeue_step(
        IsValue, ValueTransfer, Actor, Before, After).

% @latex equation:actor-configuration
% @variant selected-wake
% @lean Newspeak.SelectedActorStep.wake
% @mode selected_actor_step(+,+,+,+,+,+,+,+,+,+,-)
selected_actor_step(
    _Program, _Reification, _Materialization, _ReferenceInterpretation,
    _MessageInterpretation, _HandleInstallation, IsValue, ValueTransfer,
    Actor, Before, After) :-
    wake_packet_dequeue_step(
        IsValue, ValueTransfer, Actor, Before, _Disposition, After).

% @latex equation:actor-configuration
% @variant action-compute
% @lean Newspeak.ActorActionStep.compute
% @mode actor_action_step(+,+,+,+,+,+,+,+,+,+,-)
actor_action_step(
    Program, Reification, Materialization, ReferenceInterpretation,
    MessageInterpretation, HandleInstallation, IsValue, ValueTransfer,
    compute_action(Actor), Before, After) :-
    selected_actor_step(
        Program, Reification, Materialization, ReferenceInterpretation,
        MessageInterpretation, HandleInstallation, IsValue, ValueTransfer,
        Actor, Before, After).

% @latex rule:Network-Deliver
% @variant action-deliver
% @lean Newspeak.ActorActionStep.deliver
% @mode actor_action_step(+,+,+,+,+,+,+,+,+,+,-)
actor_action_step(
    _Program, _Reification, _Materialization, _ReferenceInterpretation,
    _MessageInterpretation, _HandleInstallation, _IsValue, _ValueTransfer,
    deliver_action(Packet), Before, After) :-
    actor_network_delivery_step(
        packet_eligible(Before, Packet), Before, Packet, After).

% @latex equation:actor-configuration
% @variant system-step
% @lean Newspeak.ActorSystemStep
% @mode actor_system_step(+,+,+,+,+,+,+,+,+,-)
actor_system_step(
    Program, Reification, Materialization, ReferenceInterpretation,
    MessageInterpretation, HandleInstallation, IsValue, ValueTransfer,
    Before, After) :-
    actor_action_step(
        Program, Reification, Materialization, ReferenceInterpretation,
        MessageInterpretation, HandleInstallation, IsValue, ValueTransfer,
        _Action, Before, After).

% --------------------------------------------------------------------------
% Reflective authority, reads, and atomic transactions
% --------------------------------------------------------------------------

% Query targets are expanded constructor-by-constructor.  Query terms retain
% the authorizing mirror even though it does not affect the target.
% @latex equation:mirror-query-target
% @variant inspect-vm
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectVM
% @mode reflection_query_target(+,+,-)
reflection_query_target(World, inspect_vm(_Mirror), vm_target(VM)) :-
    actor_world_field(World, vm, VM).

% @latex equation:mirror-query-target
% @variant inspect-program
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectProgram
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_program(_Mirror), program_target).

% @latex equation:mirror-query-target
% @variant inspect-mixin
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectMixin
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_mixin(_Mirror, Mixin), mixin_target(Mixin)).

% @latex equation:mirror-query-target
% @variant inspect-method
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectMethod
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_method(_Mirror, Method), method_target(Method)).

% @latex equation:mirror-query-target
% @variant inspect-class
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectClass
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_class(_Mirror, Class), class_target(Class)).

% @latex equation:mirror-query-target
% @variant inspect-object
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectObject
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_object(_Mirror, Object), object_target(Object)).

% @latex equation:mirror-query-target
% @variant inspect-activation
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectActivation
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_activation(_Mirror, Activation),
                        activation_target(Activation)).

% @latex equation:mirror-query-target
% @variant inspect-actor
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.inspectActor
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, inspect_actor(_Mirror, Actor), actor_target(Actor)).

% @latex equation:mirror-query-target
% @variant enumerate-instances
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.enumerateInstancesOf
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, enumerate_instances_of(_Mirror, Class),
                        class_target(Class)).

% @latex equation:mirror-query-target
% @variant enumerate-applications
% @lean Newspeak.PrologBridge.PrologReflectionQueryTarget.enumerateApplicationsOf
% @mode reflection_query_target(+,+,-)
reflection_query_target(_World, enumerate_applications_of(_Mirror, Mixin),
                        mixin_target(Mixin)).

% Three cohort-location functions used below are proof-carrying applications;
% their searches are independently related to Lean by their own bridge.
% @latex equation:mirror-query-result
% @variant locate-class-application
% @lean Newspeak.ActorWorld.locateClassId
% @mode locate_class_id_application(+,+,+,+)
locate_class_id_application(
    locate_class_id(World, Class, Location), World, Class, Location).

% @latex equation:mirror-query-result
% @variant locate-object-application
% @lean Newspeak.ActorWorld.locateObjectReference
% @mode locate_object_reference_application(+,+,+,+)
locate_object_reference_application(
    locate_object_reference(World, Object, Location), World, Object, Location).

% @latex equation:mirror-query-result
% @variant locate-activation-application
% @lean Newspeak.ActorWorld.locateActivationId
% @mode locate_activation_id_application(+,+,+,+)
locate_activation_id_application(
    locate_activation_id(World, Activation, Location), World, Activation, Location).

% @latex equation:mirror-query-result
% @variant shared-heap
% @lean Newspeak.ActorWorld.heapAt
% @mode actor_world_heap_at(+,+,-)
actor_world_heap_at(World, shared_heap, Heap) :-
    actor_world_field(World, value_heap, Heap).

% @latex equation:mirror-query-result
% @variant actor-heap
% @lean Newspeak.ActorWorld.heapAt
% @mode actor_world_heap_at(+,+,-)
actor_world_heap_at(World, actor_heap(Actor), Heap) :-
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, Heap).

% @latex equation:mirror-query-result
% @variant inspect-vm
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectVM
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_vm(_Mirror), reflection_vm(VM, Version)) :-
    actor_world_field(World, vm, VM),
    actor_world_field(World, program_version, Version).

% @latex equation:mirror-query-result
% @variant inspect-program
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectProgram
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_program(_Mirror), reflection_program(Program)) :-
    actor_world_program(World, Program).

% @latex equation:mirror-query-result
% @variant inspect-mixin
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectMixin
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_mixin(_Mirror, Mixin),
                        reflection_mixin(Definition)) :-
    actor_world_program(World, Program),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, some(Definition)).

% @latex equation:mirror-query-result
% @variant inspect-method
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectMethod
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_method(_Mirror, Method),
                        reflection_method(Mixin, Definition, Body, Locals)) :-
    actor_world_program(World, Program),
    program_mixins(Program, Mixins),
    store_entry_keys(Mixins, MixinIds),
    find_method_definition(Program, Method, MixinIds,
                           some(pair(Mixin, Definition))),
    program_method_body(Program, Method, Body),
    program_method_locals(Program, Method, Locals).

% @latex equation:mirror-query-result
% @variant inspect-class
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectClass
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_class(_Mirror, Class),
                        reflection_class(Location, Definition)) :-
    locate_class_id_application(locate_class_id(World, Class, Location),
                                World, Class, Location),
    actor_world_heap_at(World, Location, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(Definition)).

% @latex equation:mirror-query-result
% @variant inspect-object
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectObject
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_object(_Mirror, Object),
                        reflection_object(Location, Class)) :-
    locate_object_reference_application(
        locate_object_reference(World, Object, Location),
        World, Object, Location),
    actor_world_heap_at(World, Location, Heap),
    class_of(Heap, Object, some(Class)).

% @latex equation:mirror-query-result
% @variant inspect-activation
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectActivation
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_activation(_Mirror, Activation),
                        reflection_activation(Location, Definition)) :-
    locate_activation_id_application(
        locate_activation_id(World, Activation, Location),
        World, Activation, Location),
    actor_world_heap_at(World, Location, Heap),
    heap_field(Heap, activations, Activations),
    store_lookup(Activations, Activation, some(Definition)).

% @latex equation:mirror-query-result
% @variant inspect-actor
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.inspectActor
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, inspect_actor(_Mirror, Actor),
                        reflection_actor(Allocation, RunState)) :-
    actor_allocation(World, Actor, some(Allocation)),
    actor_run_state(World, Actor, RunState).

% @latex equation:mirror-query-result
% @variant enumerate-instances
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.enumerateInstancesOf
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, enumerate_instances_of(_Mirror, Class),
                        reflection_instances(Values)) :-
    locate_class_id_application(locate_class_id(World, Class, _Location),
                                World, Class, _Location),
    all_instances_of(World, Class, Values).

% @latex equation:mirror-query-result
% @variant enumerate-applications
% @lean Newspeak.PrologBridge.PrologReflectionQueryResult.enumerateApplicationsOf
% @mode reflection_query_result(+,+,-)
reflection_query_result(World, enumerate_applications_of(_Mirror, Mixin),
                        reflection_applications(Values)) :-
    actor_world_program(World, Program),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, some(_Definition)),
    mixin_applications(World, Mixin, Values).

% Authority and query execution are proof-carrying applications of the
% formally defined containment and executable query functions.
% @latex rule:Mirror-Inspect
% @variant authority-witness
% @lean Newspeak.MirrorAuthorizes
% @mode mirror_authorizes(+,+,+,+,+,+)
mirror_authorizes(
    mirror_authorizes(World, Actor, Mirror, Target, Right),
    World, Actor, Mirror, Target, Right).

% @latex rule:Mirror-Inspect
% @variant query-execution-witness
% @lean Newspeak.ReflectionQuery.execute
% @mode reflection_query_execution(+,+,+,-)
reflection_query_execution(
    query_execution(World, Query, Result), World, Query, Result).

% @latex rule:Mirror-Inspect
% @lean Newspeak.AuthorizedReflectionRead
% @mode authorized_reflection_read(+,+,+,+,+,-)
authorized_reflection_read(
    Authorization, Execution, World, Requester, Query, Result) :-
    reflection_query_mirror(Query, Mirror),
    reflection_query_authorization_target(World, Query, Target),
    mirror_authorizes(
        Authorization, World, Requester, Mirror, Target, inspect_right),
    reflection_query_execution(Execution, World, Query, Result).

% @latex rule:Mirror-Inspect
% @variant query-mirror
% @lean Newspeak.ReflectionQuery.mirror
% @mode reflection_query_mirror(+,-)
reflection_query_mirror(
    Query, Mirror) :-
    reflection_query_projection(
        query_projection(Query, Mirror, _Target), Query, Mirror, _Target).

% The projection witness avoids duplicating the ten query constructors in the
% transaction layer; its Lean correspondence fixes both projections exactly.
% @latex rule:Mirror-Inspect
% @variant query-projection-witness
% @lean Newspeak.ReflectionQuery.authorizationTarget
% @mode reflection_query_projection(+,+,-,-)
reflection_query_projection(
    query_projection(Query, Mirror, Target), Query, Mirror, Target).

% @latex rule:Mirror-Inspect
% @variant query-target
% @lean Newspeak.ReflectionQuery.authorizationTarget
% @mode reflection_query_authorization_target(+,+,-)
reflection_query_authorization_target(World, Query, Target) :-
    reflection_query_projection(
        query_projection(Query, _Mirror, Target), Query, _Mirror, Target),
    reflection_query_world_target(
        world_target(World, Query, Target), World, Query, Target).

% @latex rule:Mirror-Inspect
% @variant world-target-witness
% @lean Newspeak.ReflectionQuery.authorizationTarget
% @mode reflection_query_world_target(+,+,+,-)
reflection_query_world_target(
    world_target(World, Query, Target), World, Query, Target).

% The source patcher, elaborator, runtime preparer, validator, and rejection
% diagnostic are explicit relation parameters.  These witnesses apply those
% fixed boundaries; they do not implement them in Prolog.

% Source-code patching follows the seven code-command constructors exactly.
% Each leaf names the corresponding executable Lean source transformer.
% @latex equation:source-patch
% @variant replace-method-body
% @lean Newspeak.IdentifiedSourceImage.replaceSourceMethodBody
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(Source, replace_method_body(_Mirror, Method, Body), Patched) :-
    source_transform_application(
        replace_source_method_body(Source, Method, Body, Patched)).

% @latex equation:source-patch
% @variant replace-method-definition
% @lean Newspeak.IdentifiedSourceImage.replaceSourceMethodDefinition
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(
    Source,
    replace_method_definition(
        _Mirror, Mixin, Method, Definition, Locals, Body), Patched) :-
    source_transform_application(
        replace_source_method_definition(
            Source, Mixin, Method, Definition, Locals, Body, Patched)).

% @latex equation:source-patch
% @variant add-method-definition
% @lean Newspeak.IdentifiedSourceImage.addSourceMethodDefinition
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(
    Source, add_method_definition(_Mirror, Mixin, Definition, Locals, Body),
    Patched) :-
    source_transform_application(
        add_source_method_definition(
            Source, Mixin, Definition, Locals, Body, Patched)).

% @latex equation:source-patch
% @variant remove-method-definition
% @lean Newspeak.IdentifiedSourceImage.removeSourceMethodDefinition
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(
    Source, remove_method_definition(_Mirror, Mixin, Method), Patched) :-
    source_transform_application(
        remove_source_method_definition(Source, Mixin, Method, Patched)).

% @latex equation:source-patch
% @variant replace-slot-declarations
% @lean Newspeak.IdentifiedSourceImage.replaceSourceSlotDeclarations
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(
    Source, replace_slot_declarations(_Mirror, Mixin, Groups), Patched) :-
    source_transform_application(
        replace_source_slot_declarations(Source, Mixin, Groups, Patched)).

% @latex equation:source-patch
% @variant replace-nested-declarations
% @lean Newspeak.IdentifiedSourceImage.replaceSourceNestedDeclarations
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(
    Source, replace_nested_declarations(_Mirror, Mixin, Declarations), Patched) :-
    source_transform_application(
        replace_source_nested_declarations(
            Source, Mixin, Declarations, Patched)).

% @latex equation:source-patch
% @variant replace-mixin-initializer
% @lean Newspeak.IdentifiedSourceImage.replaceSourceMixinInitializer
% @mode patch_source_code_command(+,+,-)
patch_source_code_command(
    Source, replace_mixin_initializer(_Mirror, Mixin, Initializer), Patched) :-
    source_transform_application(
        replace_source_mixin_initializer(
            Source, Mixin, Initializer, Patched)).

% @latex equation:source-patch
% @variant transformation-application
% @lean Newspeak.IdentifiedSourceImage.patchSourceCodeCommand
% @mode source_transform_application(+)
source_transform_application(SourceTransformation).

% @latex equation:apply-source-commands
% @variant empty
% @lean Newspeak.PrologBridge.PrologOptionFold.empty
% @mode apply_source_code_commands(+,+,-)
apply_source_code_commands(Source, [], Source).

% @latex equation:apply-source-commands
% @variant step
% @lean Newspeak.PrologBridge.PrologOptionFold.next
% @mode apply_source_code_commands(+,+,-)
apply_source_code_commands(Source, [Command | Remaining], Result) :-
    patch_source_code_command(Source, Command, Patched),
    apply_source_code_commands(Patched, Remaining, Result).

% @latex equation:patched-source-candidate
% @lean Newspeak.prepareReflection
% @mode patched_source_candidate(+,+,-)
patched_source_candidate(Source, Transaction, Candidate) :-
    filter_reflection_commands(Transaction, code, CodeCommands),
    apply_source_code_commands(Source, CodeCommands, Candidate).

% @latex equation:class-object-heap-effects
% @variant change-superclass
% @lean Newspeak.applyClassGraphCommand
% @mode class_graph_heap_effect(+,+,-)
class_graph_heap_effect(
    Heap, change_superclass(_Mirror, Class, Superclass), Updated) :-
    heap_transform_application(
        change_superclass(Heap, Class, Superclass, Updated)).

% @latex equation:class-object-heap-effects
% @variant change-enclosing-object
% @lean Newspeak.applyClassGraphCommand
% @mode class_graph_heap_effect(+,+,-)
class_graph_heap_effect(
    Heap, change_class_enclosing_object(_Mirror, Class, Object), Updated) :-
    heap_transform_application(
        change_class_enclosing_object(Heap, Class, Object, Updated)).

% @latex equation:class-object-heap-effects
% @variant change-object-class
% @lean Newspeak.applyObjectClassCommand
% @mode object_class_heap_effect(+,+,-)
object_class_heap_effect(
    Heap, change_object_class(_Mirror, Object, Class), Updated) :-
    heap_transform_application(
        change_object_class(Heap, Object, Class, Updated)).

% @latex equation:class-object-heap-effects
% @variant transformation-application
% @lean Newspeak.Heap.transformExistingClass
% @mode heap_transform_application(+)
heap_transform_application(HeapTransformation).

% @latex equation:class-object-command-folds
% @variant class-empty
% @lean Newspeak.PrologBridge.PrologOptionFold.empty
% @mode apply_class_graph_commands(+,+,-)
apply_class_graph_commands(Heap, [], Heap).

% @latex equation:class-object-command-folds
% @variant class-step
% @lean Newspeak.PrologBridge.PrologOptionFold.next
% @mode apply_class_graph_commands(+,+,-)
apply_class_graph_commands(Heap, [Command | Remaining], Result) :-
    class_graph_heap_effect(Heap, Command, Updated),
    apply_class_graph_commands(Updated, Remaining, Result).

% @latex equation:class-object-command-folds
% @variant object-empty
% @lean Newspeak.PrologBridge.PrologOptionFold.empty
% @mode apply_object_class_commands(+,+,-)
apply_object_class_commands(Heap, [], Heap).

% @latex equation:class-object-command-folds
% @variant object-step
% @lean Newspeak.PrologBridge.PrologOptionFold.next
% @mode apply_object_class_commands(+,+,-)
apply_object_class_commands(Heap, [Command | Remaining], Result) :-
    object_class_heap_effect(Heap, Command, Updated),
    apply_object_class_commands(Updated, Remaining, Result).

% @latex equation:reconcile-object-layout
% @lean Newspeak.Heap.reconcileObjectLayout
% @mode reconcile_object_layout(+,+,+,-)
reconcile_object_layout(Program, Heap, Object, Updated) :-
    heap_reconciliation_application(
        reconcile_object_layout(Program, Heap, Object, Updated)).

% @latex equation:nested-declaration-keys
% @lean Newspeak.Heap.nestedKeys?
% @mode nested_declaration_keys(+,+,+,-)
nested_declaration_keys(Program, Heap, Class, Keys) :-
    heap_reconciliation_application(
        nested_declaration_keys(Program, Heap, Class, Keys)).

% @latex equation:reconcile-nested-cache
% @lean Newspeak.Heap.reconcileNestedCache
% @mode reconcile_nested_cache(+,+,+,-)
reconcile_nested_cache(Program, Heap, Class, Updated) :-
    heap_reconciliation_application(
        reconcile_nested_cache(Program, Heap, Class, Updated)).

% @latex equation:reconciliation-phases
% @variant application
% @lean Newspeak.prepareReflectionRuntime
% @mode heap_reconciliation_application(+)
heap_reconciliation_application(Reconciliation).

% @latex equation:reconciliation-phases
% @mode reconciliation_phases(+,+,-)
% @lean Newspeak.prepareReflectionRuntime
reconciliation_phases(Program, ClassUpdated, Reconciled) :-
    heap_reconciliation_application(
        reconcile_all_object_layouts(Program, ClassUpdated, Layouts)),
    heap_reconciliation_application(
        reconcile_all_nested_caches(Program, Layouts, Reconciled)).

% @latex equation:reflective-object-slot-write
% @lean Newspeak.applyReflectiveObjectSlotCommand
% @mode reflective_object_slot_write(+,+,+,-)
reflective_object_slot_write(
    Program, Heap, object_slot_write(_Mirror, Object, Slot, Value), Updated) :-
    heap_transform_application(
        object_slot_write(Program, Heap, Object, Slot, Value, Updated)).

% @latex equation:object-slot-command-fold
% @variant empty
% @lean Newspeak.PrologBridge.PrologOptionFold.empty
% @mode apply_object_slot_commands(+,+,+,-)
apply_object_slot_commands(_Program, Heap, [], Heap).

% @latex equation:object-slot-command-fold
% @variant step
% @lean Newspeak.PrologBridge.PrologOptionFold.next
% @mode apply_object_slot_commands(+,+,+,-)
apply_object_slot_commands(Program, Heap, [Command | Remaining], Result) :-
    reflective_object_slot_write(Program, Heap, Command, Updated),
    apply_object_slot_commands(Program, Updated, Remaining, Result).

% @latex equation:activation-field-effects
% @variant parameter
% @lean Newspeak.applyActivationCommand
% @mode activation_field_effect(+,+,-)
activation_field_effect(
    Heap, activation_parameter_write(_Mirror, Activation, Parameter, Value),
    Updated) :-
    heap_transform_application(
        activation_parameter_write(
            Heap, Activation, Parameter, Value, Updated)).

% @latex equation:activation-field-effects
% @variant local
% @lean Newspeak.applyActivationCommand
% @mode activation_field_effect(+,+,-)
activation_field_effect(
    Heap, activation_local_write(_Mirror, Activation, Slot, Value), Updated) :-
    heap_transform_application(
        activation_local_write(Heap, Activation, Slot, Value, Updated)).

% @latex equation:activation-field-effects
% @variant current-class
% @lean Newspeak.applyActivationCommand
% @mode activation_field_effect(+,+,-)
activation_field_effect(
    Heap, change_activation_current_class(_Mirror, Activation, Class), Updated) :-
    heap_transform_application(
        change_activation_current_class(Heap, Activation, Class, Updated)).

% @latex equation:activation-field-effects
% @variant continuation
% @lean Newspeak.applyActivationCommand
% @mode activation_field_effect(+,+,-)
activation_field_effect(
    Heap, change_activation_continuation(
        _Mirror, Activation, Continuation), Updated) :-
    heap_transform_application(
        change_activation_continuation(
            Heap, Activation, Continuation, Updated)).

% @latex equation:activation-field-effects
% @variant uncontinuable
% @lean Newspeak.applyActivationCommand
% @mode activation_field_effect(+,+,-)
activation_field_effect(
    Heap, make_activation_uncontinuable(_Mirror, Activation), Updated) :-
    heap_transform_application(
        make_activation_uncontinuable(Heap, Activation, Updated)).

% @latex equation:activation-command-fold
% @variant empty
% @lean Newspeak.PrologBridge.PrologOptionFold.empty
% @mode apply_activation_commands(+,+,-)
apply_activation_commands(Heap, [], Heap).

% @latex equation:activation-command-fold
% @variant step
% @lean Newspeak.PrologBridge.PrologOptionFold.next
% @mode apply_activation_commands(+,+,-)
apply_activation_commands(Heap, [Command | Remaining], Result) :-
    activation_field_effect(Heap, Command, Updated),
    apply_activation_commands(Updated, Remaining, Result).

% @latex equation:reflective-continuation-transfer
% @lean Newspeak.ActorWorld.applyContinuationTransfer
% @mode reflective_continuation_transfer(+,+,-)
reflective_continuation_transfer(
    World, continue_at_activation(_Mirror, Actor, Activation, Value), Updated) :-
    world_transform_application(
        continuation_transfer(
            World, Actor, Activation, Value, Updated)).

% @latex equation:reflective-continuation-transfer
% @variant world-transformation-application
% @lean Newspeak.ActorWorld.applyContinuationTransfer
% @mode world_transform_application(+)
world_transform_application(WorldTransformation).

% @latex equation:continuation-command-fold
% @variant empty
% @lean Newspeak.PrologBridge.PrologOptionFold.empty
% @mode apply_continuation_commands(+,+,-)
apply_continuation_commands(World, [], World).

% @latex equation:continuation-command-fold
% @variant step
% @lean Newspeak.PrologBridge.PrologOptionFold.next
% @mode apply_continuation_commands(+,+,-)
apply_continuation_commands(World, [Command | Remaining], Result) :-
    reflective_continuation_transfer(World, Command, Updated),
    apply_continuation_commands(Updated, Remaining, Result).

% @latex equation:debugger-command-fold
% @variant empty
% @lean Newspeak.applyDebuggerCommandSequence
% @mode apply_debugger_commands(+,+,+,+,-)
apply_debugger_commands(_Program, _Requester, World, [], World).

% @latex equation:debugger-command-fold
% @variant step
% @lean Newspeak.applyDebuggerCommandSequence
% @mode apply_debugger_commands(+,+,+,+,-)
apply_debugger_commands(
    Program, Requester, World, [Command | Remaining], Result) :-
    debugger_command_effect(Program, Requester, World, Command, Updated),
    apply_debugger_commands(Program, Requester, Updated, Remaining, Result).

% @latex equation:debugger-command-fold
% @variant effect-application
% @lean Newspeak.applyDebuggerCommand
% @mode debugger_command_effect(+,+,+,+,-)
debugger_command_effect(Program, Requester, World, Command, Updated) :-
    world_transform_application(
        debugger_command(Program, Requester, World, Command, Updated)).

% @latex equation:resolve-stack-template-keys
% @lean Newspeak.resolveTemplateKeys
% @mode resolve_stack_template_keys(+,+,-)
resolve_stack_template_keys(Allocation, Template, Resolution) :-
    stack_materialization_application(
        resolve_template_keys(Allocation, Template, Resolution)).

% @latex equation:debug-stack-image-validity
% @lean Newspeak.decodeControlImage
% @mode debug_stack_image_validity(+,+,+)
debug_stack_image_validity(Program, Heap, Images) :-
    stack_materialization_application(
        debug_stack_image_validity(Program, Heap, Images)).

% @latex equation:retire-removed-stack-activations
% @variant empty
% @lean Newspeak.Heap.retireRemovedActivations
% @mode retire_removed_stack_activations(+,+,-)
retire_removed_stack_activations(Heap, [], Heap).

% @latex equation:retire-removed-stack-activations
% @variant step
% @lean Newspeak.Heap.retireRemovedActivations
% @mode retire_removed_stack_activations(+,+,-)
retire_removed_stack_activations(Heap, [Activation | Remaining], Result) :-
    heap_transform_application(
        retire_activation(Heap, Activation, Retired)),
    retire_removed_stack_activations(Retired, Remaining, Result).

% @latex equation:materialize-stack-template
% @lean Newspeak.materializeStackTemplate
% @mode materialize_stack_template(+,+,+,+,-,-,-)
materialize_stack_template(
    Program, Allocation, OldStack, Template,
    UpdatedAllocation, NewStack, NewControl) :-
    stack_materialization_application(
        materialize_stack_template(
            Program, Allocation, OldStack, Template,
            UpdatedAllocation, NewStack, NewControl)).

% @latex equation:materialize-stack-template
% @variant application
% @lean Newspeak.materializeStackTemplate
% @mode stack_materialization_application(+)
stack_materialization_application(Materialization).

% The five command equations are kept distinct even though they share the
% executable `applyDebuggerCommand` implementation.
% @latex equation:pause-actor-effect
% @lean Newspeak.applyDebuggerCommand
% @mode pause_actor_effect(+,+,+,+,-)
pause_actor_effect(Program, Requester, World,
                   pause_actor(Mirror, Actor, Reason), Updated) :-
    debugger_command_effect(
        Program, Requester, World,
        pause_actor(Mirror, Actor, Reason), Updated).

% @latex equation:replace-current-actor-stack
% @lean Newspeak.applyDebuggerCommand
% @mode replace_current_actor_stack(+,+,+,+,-)
replace_current_actor_stack(
    Program, Requester, World,
    replace_current_actor_stack(Mirror, Actor, Template), Updated) :-
    debugger_command_effect(
        Program, Requester, World,
        replace_current_actor_stack(Mirror, Actor, Template), Updated).

% @latex equation:resume-exception-stack-template
% @lean Newspeak.popStackFrames
% @mode resume_exception_stack_template(+,+,+,-)
resume_exception_stack_template(Stack, Activation, Value, Resumed) :-
    list_append(Prefix, [Frame | Suffix], Stack),
    frame_template_key(Frame, retain(Activation)),
    promote_frame(Frame, Value, Promoted),
    list_append(Prefix, [Promoted], Resumed),
    list_suffix_witness(Suffix).

% @latex equation:resume-exception-stack-template
% @variant key
% @lean Newspeak.FrameTemplate.key
% @mode frame_template_key(+,-)
frame_template_key(frame_template(Key, _Record, _Control), Key).

% @latex equation:resume-exception-stack-template
% @variant suffix-witness-empty
% @lean Newspeak.StackTemplate
% @mode list_suffix_witness(+)
list_suffix_witness([]).

% @latex equation:resume-exception-stack-template
% @variant suffix-witness-step
% @lean Newspeak.StackTemplate
% @mode list_suffix_witness(+)
list_suffix_witness([_Head | Tail]) :-
    list_suffix_witness(Tail).

% @latex equation:replace-paused-actor-stack
% @lean Newspeak.applyDebuggerCommand
% @mode replace_paused_actor_stack(+,+,+,+,-)
replace_paused_actor_stack(
    Program, Requester, World,
    replace_paused_actor_stack(Mirror, Actor, Token, Template), Updated) :-
    debugger_command_effect(
        Program, Requester, World,
        replace_paused_actor_stack(Mirror, Actor, Token, Template), Updated).

% @latex equation:resume-paused-actor-full-speed
% @lean Newspeak.applyDebuggerCommand
% @mode resume_paused_actor_full_speed(+,+,+,+,-)
resume_paused_actor_full_speed(
    Program, Requester, World,
    resume_paused_actor_at_full_speed(Mirror, Actor, Token), Updated) :-
    debugger_command_effect(
        Program, Requester, World,
        resume_paused_actor_at_full_speed(Mirror, Actor, Token), Updated).

% @latex equation:replace-resume-paused-actor-stack
% @lean Newspeak.applyDebuggerCommand
% @mode replace_resume_paused_actor_stack(+,+,+,+,-)
replace_resume_paused_actor_stack(
    Program, Requester, World,
    replace_and_resume_paused_actor_stack(
        Mirror, Actor, Token, Template), Updated) :-
    debugger_command_effect(
        Program, Requester, World,
        replace_and_resume_paused_actor_stack(
            Mirror, Actor, Token, Template), Updated).

% --------------------------------------------------------------------------
% Reflection validation and diagnostics
% --------------------------------------------------------------------------

% @latex equation:fresh-installed-activations
% @lean Newspeak.ActorWorld.liveActivationIds
% @mode fresh_installed_activations(+,+,+,-)
fresh_installed_activations(Before, After, Actor, Fresh) :-
    actor_run_state(After, Actor, some(State)),
    run_state_activation_ids(State, AfterIds),
    actor_world_vm_store_domain(Before, Existing),
    list_difference(AfterIds, Existing, Fresh).

% @latex equation:fresh-installed-activations
% @variant vm-domain-application
% @lean Newspeak.ActorWorld.allCohortInstancesOf
% @mode actor_world_vm_store_domain(+,-)
actor_world_vm_store_domain(World, Domain) :-
    validation_application(vm_store_domain(World, Domain)).

% @latex equation:reflective-record-id-sets
% @variant classes
% @lean Newspeak.Heap.classes
% @mode class_record_ids(+,-)
class_record_ids(Heap, Ids) :-
    heap_field(Heap, classes, store(Entries)),
    store_entry_keys(Entries, Ids).

% @latex equation:reflective-record-id-sets
% @variant objects
% @lean Newspeak.Heap.objects
% @mode ordinary_object_ids(+,-)
ordinary_object_ids(Heap, Ids) :-
    heap_field(Heap, objects, store(Entries)),
    store_entry_keys(Entries, Ids).

% @latex equation:reflective-record-id-sets
% @variant activations
% @lean Newspeak.Heap.activations
% @mode activation_record_ids(+,-)
activation_record_ids(Heap, Ids) :-
    heap_field(Heap, activations, store(Entries)),
    store_entry_keys(Entries, Ids).

% @latex equation:reflective-class-chain-validity
% @lean Newspeak.Program.ClassChain
% @mode reflective_reaches_top(+,+,+)
reflective_reaches_top(Program, Heap, Class) :-
    validation_application(reaches_top(Program, Heap, Class)).

% @latex equation:reflective-class-record-validity
% @lean Newspeak.ReflectionClassGraphsOK
% @mode reflective_class_record_valid(+,+,+)
reflective_class_record_valid(Program, Heap, Class) :-
    validation_application(class_record_valid(Program, Heap, Class)).

% @latex equation:reflective-class-graph-validity
% @lean Newspeak.ReflectionClassGraphsOK
% @mode reflective_class_graph_valid(+,+)
reflective_class_graph_valid(Program, Heap) :-
    validation_application(class_graph_valid(Program, Heap)).

% @latex equation:class-origin-declaration
% @variant expression
% @lean Newspeak.ClassOrigin.expression
% @mode class_origin_declaration(+,-)
class_origin_declaration(expression_origin(Declaration), Declaration).

% @latex equation:class-origin-declaration
% @variant actor
% @lean Newspeak.ClassOrigin.actor
% @mode class_origin_declaration(+,-)
class_origin_declaration(actor_origin(Declaration), Declaration).

% @latex equation:cached-nested-class-validity
% @lean Newspeak.Heap.ReflectionNestedCachesOK
% @mode cached_nested_class_valid(+,+,+)
cached_nested_class_valid(Heap, Object, Declaration) :-
    validation_application(
        cached_nested_class_valid(Heap, Object, Declaration)).

% @latex equation:reflective-object-record-validity
% @lean Newspeak.Heap.ReflectionObjectLayoutsOK
% @mode reflective_object_record_valid(+,+,+)
reflective_object_record_valid(Program, Heap, Object) :-
    validation_application(object_record_valid(Program, Heap, Object)).

% @latex equation:reflective-object-validity
% @lean Newspeak.ReflectionObjectStoresOK
% @mode reflective_object_store_valid(+,+)
reflective_object_store_valid(Program, Heap) :-
    validation_application(object_store_valid(Program, Heap)).

% @latex equation:live-activation-record-validity
% @lean Newspeak.ReflectionLiveActivationsOK
% @mode live_activation_record_valid(+,+,+,+)
live_activation_record_valid(Program, Heap, World, Activation) :-
    validation_application(
        live_activation_record_valid(Program, Heap, World, Activation)).

% @latex equation:live-activation-validity
% @lean Newspeak.ReflectionLiveActivationsOK
% @mode live_activations_valid(+,+,+)
live_activations_valid(Program, Heap, World) :-
    validation_application(live_activations_valid(Program, Heap, World)).

% The five command-specific predicates keep their command shapes visible.
% @latex equation:activation-parameter-edit-validity
% @lean Newspeak.ReflectionActivationEditsOK
% @mode activation_edit_valid(+,+,+,+)
activation_edit_valid(
    BeforeHeap, AfterHeap, AfterWorld,
    activation_parameter_write(Mirror, Activation, Parameter, Value)) :-
    validation_application(
        activation_parameter_edit_valid(
            BeforeHeap, AfterHeap, AfterWorld, Mirror,
            Activation, Parameter, Value)).

% @latex equation:activation-local-edit-validity
% @lean Newspeak.ReflectionActivationEditsOK
% @mode activation_edit_valid(+,+,+,+)
activation_edit_valid(
    BeforeHeap, AfterHeap, AfterWorld,
    activation_local_write(Mirror, Activation, Slot, Value)) :-
    validation_application(
        activation_local_edit_valid(
            BeforeHeap, AfterHeap, AfterWorld, Mirror,
            Activation, Slot, Value)).

% @latex equation:activation-class-edit-validity
% @lean Newspeak.ReflectionActivationEditsOK
% @mode activation_edit_valid(+,+,+,+)
activation_edit_valid(
    BeforeHeap, AfterHeap, AfterWorld,
    change_activation_current_class(Mirror, Activation, Class)) :-
    validation_application(
        activation_class_edit_valid(
            BeforeHeap, AfterHeap, AfterWorld, Mirror,
            Activation, Class)).

% @latex equation:activation-continuation-edit-validity
% @lean Newspeak.ReflectionActivationEditsOK
% @mode activation_edit_valid(+,+,+,+)
activation_edit_valid(
    BeforeHeap, AfterHeap, AfterWorld,
    change_activation_continuation(Mirror, Activation, Continuation)) :-
    validation_application(
        activation_continuation_edit_valid(
            BeforeHeap, AfterHeap, AfterWorld, Mirror,
            Activation, Continuation)).

% @latex equation:activation-uncontinuable-edit-validity
% @lean Newspeak.ReflectionActivationEditsOK
% @mode activation_edit_valid(+,+,+,+)
activation_edit_valid(
    BeforeHeap, AfterHeap, AfterWorld,
    make_activation_uncontinuable(Mirror, Activation)) :-
    validation_application(
        activation_uncontinuable_edit_valid(
            BeforeHeap, AfterHeap, AfterWorld, Mirror, Activation)).

% @latex equation:continuation-transfer-count
% @variant empty
% @lean Newspeak.ReflectionActivationEditsOK
% @mode continuation_transfer_count(+,+,-)
continuation_transfer_count([], _Actor, zero).

% @latex equation:continuation-transfer-count
% @variant matching-transfer
% @lean Newspeak.ReflectionActivationEditsOK
% @mode continuation_transfer_count(+,+,-)
continuation_transfer_count(
    [continue_at_activation(_Mirror, Actor, _Activation, _Value) | Remaining],
    Actor, succ(Count)) :-
    continuation_transfer_count(Remaining, Actor, Count).

% @latex equation:continuation-transfer-count
% @variant other-actor-transfer
% @lean Newspeak.ReflectionActivationEditsOK
% @mode continuation_transfer_count(+,+,-)
continuation_transfer_count(
    [continue_at_activation(_Mirror, Other, _Activation, _Value) | Remaining],
    Actor, Count) :-
    dif(Actor, Other),
    continuation_transfer_count(Remaining, Actor, Count).

% @latex equation:continuation-transfer-count
% @variant non-transfer
% @lean Newspeak.ReflectionActivationEditsOK
% @mode continuation_transfer_count(+,+,-)
continuation_transfer_count([Command | Remaining], Actor, Count) :-
    reflection_command_family(Command, Family),
    dif(Family, continuation),
    continuation_transfer_count(Remaining, Actor, Count).

% @latex equation:activation-transaction-validity
% @lean Newspeak.ReflectionActivationEditsOK
% @mode activation_transaction_valid(+,+,+)
activation_transaction_valid(Before, Transaction, After) :-
    validation_application(
        activation_transaction_valid(Before, Transaction, After)).

% A concrete, inspectable structural extractor for the generic Prolog term
% representation used by the bridge.
% @latex equation:structural-reference-extractor
% @variant reference
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_references(+,-)
structural_references(reference(Reference), [Reference]).

% @latex equation:structural-reference-extractor
% @variant atom
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_references(+,-)
structural_references(atom(_Atomic), []).

% @latex equation:structural-reference-extractor
% @variant constructor
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_references(+,-)
structural_references(constructor(_Name, Arguments), References) :-
    structural_reference_list(Arguments, Raw),
    list_deduplicated(Raw, References).

% @latex equation:structural-reference-extractor
% @variant map
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_references(+,-)
structural_references(finite_map(Entries), References) :-
    structural_reference_entries(Entries, Raw),
    list_deduplicated(Raw, References).

% @latex equation:structural-reference-extractor
% @variant list-empty
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_reference_list(+,-)
structural_reference_list([], []).

% @latex equation:structural-reference-extractor
% @variant list-step
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_reference_list(+,-)
structural_reference_list([Value | Remaining], References) :-
    structural_references(Value, Current),
    structural_reference_list(Remaining, Later),
    list_append(Current, Later, References).

% @latex equation:structural-reference-extractor
% @variant entries-empty
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_reference_entries(+,-)
structural_reference_entries([], []).

% @latex equation:structural-reference-extractor
% @variant entries-step
% @lean Newspeak.Heap.recordStrongReferences
% @mode structural_reference_entries(+,-)
structural_reference_entries([entry(Key, Value) | Remaining], References) :-
    structural_references(Key, KeyReferences),
    structural_references(Value, ValueReferences),
    structural_reference_entries(Remaining, Later),
    list_append(KeyReferences, ValueReferences, EntryReferences),
    list_append(EntryReferences, Later, References).

% @latex equation:reflective-actor-isolation
% @lean Newspeak.ReflectionActorIsolationOK
% @mode reflective_actor_isolation(+)
reflective_actor_isolation(World) :-
    validation_application(actor_isolation_valid(World)).

% @latex equation:failed-reflection-validations
% @lean Newspeak.concreteReflectionValidator
% @mode failed_reflection_validations(+,+,+,-)
failed_reflection_validations(Before, Transaction, After, Failed) :-
    validation_application(
        failed_reflection_validations(Before, Transaction, After, Failed)).

% @latex equation:reflection-error-index-sets
% @variant unauthorized
% @lean Newspeak.ReflectionTransactionAuthorized
% @mode reflection_unauthorized_indices(+,+,+,-)
reflection_unauthorized_indices(World, Requester, Transaction, Indices) :-
    validation_application(
        unauthorized_indices(World, Requester, Transaction, Indices)).

% @latex equation:reflection-error-index-sets
% @variant conflicts
% @lean Newspeak.PrologBridge.PrologReflectionConflictAt
% @mode reflection_conflict_pairs(+,-)
reflection_conflict_pairs(Transaction, Pairs) :-
    validation_application(conflict_pairs(Transaction, Pairs)).

% @latex equation:reflection-diagnostic-candidates
% @variant source
% @lean Newspeak.IdentifiedSourceImage.applySourceCodeCommands
% @mode reflection_source_candidate(+,+,-)
reflection_source_candidate(Source, Transaction, Candidate) :-
    patched_source_candidate(Source, Transaction, Candidate).

% @latex equation:reflection-diagnostic-candidates
% @variant program
% @lean Newspeak.IdentifiedSourceImage.reelaborateInstalledProgram
% @mode reflection_program_candidate(+,+,-)
reflection_program_candidate(Source, Transaction, Program) :-
    reflection_source_candidate(Source, Transaction, Candidate),
    validation_application(reelaborated_program(Candidate, Program)).

% @latex equation:reflection-version-observation
% @variant materialized-control
% @lean Newspeak.MaterializedControlPreserved
% @mode reflection_version_observation(+,+)
reflection_version_observation(
    materialized_control(Stack, Control), retained_control(Stack, Control)).

% @latex equation:reflection-version-observation
% @variant future-resolution
% @lean Newspeak.prepareReflection_increments_version_exactly_once
% @mode reflection_version_observation(+,+)
reflection_version_observation(future_method_resolution, updated_program).

% @latex equation:reflection-version-observation
% @variant undispatched-packet
% @lean Newspeak.prepareReflection_increments_version_exactly_once
% @mode reflection_version_observation(+,+)
reflection_version_observation(undispatched_packet, updated_program_at_turn).

% @latex equation:reflection-version-observation
% @variant allocated-closure
% @lean Newspeak.ClosureDef
% @mode reflection_version_observation(+,+)
reflection_version_observation(
    allocated_closure(Body), retained_closure_body(Body)).

% @latex equation:reflection-version-observation
% @variant stable-identity
% @lean Newspeak.ClassOrigin
% @mode reflection_version_observation(+,+)
reflection_version_observation(
    stable_identity(Identity), updated_record(Identity)).

% @latex equation:reflective-class-graph-validity
% @variant validation-application
% @lean Newspeak.concreteReflectionValidator
% @mode validation_application(+)
validation_application(Validation).

% List difference is constructive and preserves the order of its first input.
% @latex equation:fresh-installed-activations
% @variant difference-empty
% @lean Newspeak.FiniteStore.containsKey
% @mode list_difference(+,+,-)
list_difference([], _Removed, []).

% @latex equation:fresh-installed-activations
% @variant difference-drop
% @lean Newspeak.FiniteStore.containsKey
% @mode list_difference(+,+,-)
list_difference([Head | Tail], Removed, Result) :-
    list_member(Head, Removed),
    list_difference(Tail, Removed, Result).

% @latex equation:fresh-installed-activations
% @variant difference-keep
% @lean Newspeak.FiniteStore.containsKey
% @mode list_difference(+,+,-)
list_difference([Head | Tail], Removed, [Head | Result]) :-
    list_not_member(Head, Removed),
    list_difference(Tail, Removed, Result).

% --------------------------------------------------------------------------
% Weak containers and optional garbage collection
% --------------------------------------------------------------------------

% @latex equation:weak-container-validity
% @variant array-empty
% @lean Newspeak.WeakContainer.ReferencesAreLive
% @mode weak_container_references_live(+,+)
weak_container_references_live(_Heap, weak_array([])).

% @latex equation:weak-container-validity
% @variant array-step
% @lean Newspeak.WeakContainer.ReferencesAreLive
% @mode weak_container_references_live(+,+)
weak_container_references_live(Heap, weak_array([Reference | Remaining])) :-
    class_of(Heap, Reference, some(_Class)),
    weak_container_references_live(Heap, weak_array(Remaining)).

% @latex equation:weak-container-validity
% @variant map-empty
% @lean Newspeak.WeakContainer.ReferencesAreLive
% @mode weak_container_references_live(+,+)
weak_container_references_live(_Heap, weak_map(store([]))).

% @latex equation:weak-container-validity
% @variant map-step
% @lean Newspeak.WeakContainer.ReferencesAreLive
% @mode weak_container_references_live(+,+)
weak_container_references_live(
    Heap, weak_map(store([entry(Key, Value) | Remaining]))) :-
    class_of(Heap, Key, some(_KeyClass)),
    class_of(Heap, Value, some(_ValueClass)),
    weak_container_references_live(Heap, weak_map(store(Remaining))).

% @latex equation:weak-container-validity
% @variant heap
% @lean Newspeak.Heap.WeakContainersWellFormed
% @mode weak_containers_valid(+)
weak_containers_valid(Heap) :-
    heap_field(Heap, objects, store(Entries)),
    weak_object_entries_valid(Heap, Entries).

% @latex equation:weak-container-validity
% @variant objects-empty
% @lean Newspeak.Heap.WeakContainersWellFormed
% @mode weak_object_entries_valid(+,+)
weak_object_entries_valid(_Heap, []).

% @latex equation:weak-container-validity
% @variant object-none
% @lean Newspeak.Heap.WeakContainersWellFormed
% @mode weak_object_entries_valid(+,+)
weak_object_entries_valid(
    Heap, [entry(_Object, object_def(_Class, _Slots, _Nested, none)) | Tail]) :-
    weak_object_entries_valid(Heap, Tail).

% @latex equation:weak-container-validity
% @variant object-container
% @lean Newspeak.Heap.WeakContainersWellFormed
% @mode weak_object_entries_valid(+,+)
weak_object_entries_valid(
    Heap,
    [entry(_Object,
           object_def(_Class, _Slots, _Nested, some(Container))) | Tail]) :-
    weak_container_references_live(Heap, Container),
    weak_object_entries_valid(Heap, Tail).

% @latex equation:weak-array-operations
% @variant read
% @lean Newspeak.Heap.readWeakArrayCell
% @mode weak_array_read(+,+,+,-)
weak_array_read(Heap, Object, Index, Value) :-
    heap_field(Heap, objects, Objects),
    store_lookup(
        Objects, Object,
        some(object_def(_Class, _Slots, _Nested,
                        some(weak_array(Elements))))),
    list_nth_zero_based(Elements, Index, Value).

% @latex equation:weak-array-operations
% @variant write
% @lean Newspeak.Heap.writeWeakArrayCell
% @mode write_weak_array_cell(+,+,+,+,-)
write_weak_array_cell(Heap, Object, Index, Value, UpdatedHeap) :-
    heap_field(Heap, objects, Objects),
    store_lookup(
        Objects, Object,
        some(object_def(Class, Slots, Nested,
                        some(weak_array(Elements))))),
    list_set_zero_based(Elements, Index, Value, UpdatedElements),
    store_install(
        Objects, Object,
        object_def(Class, Slots, Nested, some(weak_array(UpdatedElements))),
        UpdatedObjects),
    heap_install_field(Heap, objects, UpdatedObjects, UpdatedHeap).

% @latex equation:weak-map-operations
% @variant lookup-present
% @lean Newspeak.Heap.lookupWeakMapEntry
% @mode weak_map_lookup(+,+,+,-)
weak_map_lookup(Heap, Object, Key, Value) :-
    heap_field(Heap, objects, Objects),
    store_lookup(
        Objects, Object,
        some(object_def(_Class, _Slots, _Nested,
                        some(weak_map(Entries))))),
    store_lookup(Entries, Key, some(Value)).

% @latex equation:weak-map-operations
% @variant lookup-absent
% @lean Newspeak.Heap.lookupWeakMapEntry
% @mode weak_map_lookup(+,+,+,-)
weak_map_lookup(Heap, Object, Key, nil_object) :-
    heap_field(Heap, objects, Objects),
    store_lookup(
        Objects, Object,
        some(object_def(_Class, _Slots, _Nested,
                        some(weak_map(Entries))))),
    store_lookup(Entries, Key, none).

% @latex equation:weak-map-operations
% @variant write
% @lean Newspeak.Heap.writeWeakMapEntry
% @mode write_weak_map_entry(+,+,+,+,-)
write_weak_map_entry(Heap, Object, Key, Value, UpdatedHeap) :-
    heap_field(Heap, objects, Objects),
    store_lookup(
        Objects, Object,
        some(object_def(Class, Slots, Nested, some(weak_map(Entries))))),
    store_install(Entries, Key, Value, UpdatedEntries),
    store_install(
        Objects, Object,
        object_def(Class, Slots, Nested, some(weak_map(UpdatedEntries))),
        UpdatedObjects),
    heap_install_field(Heap, objects, UpdatedObjects, UpdatedHeap).

% @latex equation:weak-array-operations
% @variant heap-install-field
% @lean Newspeak.Heap.installObject
% @mode heap_install_field(+,+,+,-)
heap_install_field(heap(Fields), Name, Value, heap(Updated)) :-
    store_install(Fields, Name, Value, Updated).

% @latex equation:weak-array-operations
% @variant nth-zero
% @lean List.getElem?
% @mode list_nth_zero_based(+,+,-)
list_nth_zero_based([Element | _Tail], zero, Element).

% @latex equation:weak-array-operations
% @variant nth-successor
% @lean List.getElem?
% @mode list_nth_zero_based(+,+,-)
list_nth_zero_based([_Element | Tail], succ(Index), Result) :-
    list_nth_zero_based(Tail, Index, Result).

% @latex equation:weak-array-operations
% @variant set-zero
% @lean List.set
% @mode list_set_zero_based(+,+,+,-)
list_set_zero_based([_Old | Tail], zero, Value, [Value | Tail]).

% @latex equation:weak-array-operations
% @variant set-successor
% @lean List.set
% @mode list_set_zero_based(+,+,+,-)
list_set_zero_based([Head | Tail], succ(Index), Value, [Head | Updated]) :-
    list_set_zero_based(Tail, Index, Value, Updated).

% @latex equation:gc-strong-payload
% @variant weak-array
% @lean Newspeak.Heap.collectWeakContainer
% @mode gc_strong_payload(+,-)
gc_strong_payload(
    object_def(Class, Slots, Nested, some(weak_array(Elements))),
    object_def(Class, Slots, Nested, some(weak_array(Nils)))) :-
    nil_list_like(Elements, Nils).

% @latex equation:gc-strong-payload
% @variant weak-map
% @lean Newspeak.Heap.collectWeakContainer
% @mode gc_strong_payload(+,-)
gc_strong_payload(
    object_def(Class, Slots, Nested, some(weak_map(_Entries))),
    object_def(Class, Slots, Nested, some(weak_map(store([]))))).

% @latex equation:gc-strong-payload
% @variant other-record
% @lean Newspeak.Heap.collectObjectDef
% @mode gc_strong_payload(+,-)
gc_strong_payload(Record, Record) :-
    gc_nonweak_record(Record).

% @latex equation:gc-strong-payload
% @variant nil-list-empty
% @lean List.map
% @mode nil_list_like(+,-)
nil_list_like([], []).

% @latex equation:gc-strong-payload
% @variant nil-list-step
% @lean List.map
% @mode nil_list_like(+,-)
nil_list_like([_Element | Tail], [nil_object | Nils]) :-
    nil_list_like(Tail, Nils).

% @latex equation:gc-strong-payload
% @variant nonweak-application
% @lean Newspeak.Heap.collectObjectDef
% @mode gc_nonweak_record(+)
gc_nonweak_record(Record) :-
    gc_application(nonweak_record(Record)).

% @latex equation:gc-roots-and-successors
% @variant roots
% @lean Newspeak.runtimeObjectRoots
% @mode gc_roots(+,+,-)
gc_roots(World, HostRoots, Roots) :-
    gc_application(control_references(World, ControlReferences)),
    actor_world_vm_store_domain(World, Domain),
    list_append(HostRoots, ControlReferences, Candidates),
    list_deduplicated(Candidates, Distinct),
    list_intersection(Distinct, Domain, Roots).

% @latex equation:gc-roots-and-successors
% @variant strong-successors
% @lean Newspeak.Heap.recordStrongReferences
% @mode gc_strong_successors(+,+,-)
gc_strong_successors(World, Reference, Successors) :-
    gc_application(runtime_payload(World, Reference, Payload)),
    gc_strong_payload(Payload, StrongPayload),
    structural_references(StrongPayload, References),
    actor_world_vm_store_domain(World, Domain),
    list_intersection(References, Domain, Successors).

% @latex equation:gc-roots-and-successors
% @variant enabled-map-values
% @lean Newspeak.Heap.enabledWeakMapValues
% @mode gc_enabled_map_values(+,+,+,-)
gc_enabled_map_values(World, Reference, Reached, Values) :-
    gc_application(runtime_payload(
        World, Reference,
        object_def(_Class, _Slots, _Nested, some(weak_map(store(Entries)))))),
    enabled_weak_map_entries(Entries, Reached, Values).

% @latex equation:gc-roots-and-successors
% @variant enabled-map-empty
% @lean Newspeak.Heap.enabledWeakMapValues
% @mode enabled_weak_map_entries(+,+,-)
enabled_weak_map_entries([], _Reached, []).

% @latex equation:gc-roots-and-successors
% @variant enabled-map-retained
% @lean Newspeak.Heap.enabledWeakMapValues
% @mode enabled_weak_map_entries(+,+,-)
enabled_weak_map_entries(
    [entry(Key, Value) | Tail], Reached, [Value | Values]) :-
    list_member(Key, Reached),
    enabled_weak_map_entries(Tail, Reached, Values).

% @latex equation:gc-roots-and-successors
% @variant enabled-map-disabled
% @lean Newspeak.Heap.enabledWeakMapValues
% @mode enabled_weak_map_entries(+,+,-)
enabled_weak_map_entries([entry(Key, _Value) | Tail], Reached, Values) :-
    list_not_member(Key, Reached),
    enabled_weak_map_entries(Tail, Reached, Values).

% @latex equation:gc-reachability
% @variant zero
% @lean Newspeak.Heap.ConditionallyReachableWithin
% @mode gc_reachability_stage(+,+,+,-)
gc_reachability_stage(World, HostRoots, zero, Roots) :-
    gc_roots(World, HostRoots, Roots).

% @latex equation:gc-reachability
% @variant successor
% @lean Newspeak.Heap.ConditionallyReachableWithin
% @mode gc_reachability_stage(+,+,+,-)
gc_reachability_stage(World, HostRoots, succ(Depth), Reached) :-
    gc_reachability_stage(World, HostRoots, Depth, Previous),
    gc_application(expand_reachability(World, Previous, Expanded)),
    list_append(Previous, Expanded, Candidates),
    list_deduplicated(Candidates, Reached).

% @latex equation:gc-reachability
% @variant live-fixed-point
% @lean Newspeak.Heap.conditionallyReachableReferences
% @mode gc_live_references(+,+,-)
gc_live_references(World, HostRoots, Live) :-
    gc_application(gc_live_references(World, HostRoots, Live)).

% @latex equation:gc-reachability
% @variant garbage
% @lean Newspeak.Heap.conditionallyReachableReferences
% @mode gc_garbage_references(+,+,-)
gc_garbage_references(World, HostRoots, Garbage) :-
    actor_world_vm_store_domain(World, Domain),
    gc_live_references(World, HostRoots, Live),
    list_difference(Domain, Live, Garbage).

% @latex equation:gc-clear-weak-payload
% @variant array
% @lean Newspeak.Heap.collectWeakContainer
% @mode gc_clear_weak_payload(+,+,-)
gc_clear_weak_payload(
    Garbage, object_def(Class, Slots, Nested, some(weak_array(Elements))),
    object_def(Class, Slots, Nested, some(weak_array(Cleared)))) :-
    clear_weak_array_elements(Garbage, Elements, Cleared).

% @latex equation:gc-clear-weak-payload
% @variant map
% @lean Newspeak.Heap.collectWeakContainer
% @mode gc_clear_weak_payload(+,+,-)
gc_clear_weak_payload(
    Garbage, object_def(Class, Slots, Nested, some(weak_map(store(Entries)))),
    object_def(Class, Slots, Nested, some(weak_map(store(Cleared))))) :-
    clear_weak_map_entries(Garbage, Entries, Cleared).

% @latex equation:gc-clear-weak-payload
% @variant other
% @lean Newspeak.Heap.collectObjectDef
% @mode gc_clear_weak_payload(+,+,-)
gc_clear_weak_payload(_Garbage, Record, Record) :-
    gc_nonweak_record(Record).

% @latex equation:gc-clear-weak-payload
% @variant array-empty
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_array_elements(+,+,-)
clear_weak_array_elements(_Garbage, [], []).

% @latex equation:gc-clear-weak-payload
% @variant array-collected
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_array_elements(+,+,-)
clear_weak_array_elements(
    Garbage, [Reference | Tail], [nil_object | Cleared]) :-
    list_member(Reference, Garbage),
    clear_weak_array_elements(Garbage, Tail, Cleared).

% @latex equation:gc-clear-weak-payload
% @variant array-retained
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_array_elements(+,+,-)
clear_weak_array_elements(
    Garbage, [Reference | Tail], [Reference | Cleared]) :-
    list_not_member(Reference, Garbage),
    clear_weak_array_elements(Garbage, Tail, Cleared).

% @latex equation:gc-clear-weak-payload
% @variant map-empty
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_map_entries(+,+,-)
clear_weak_map_entries(_Garbage, [], []).

% @latex equation:gc-clear-weak-payload
% @variant map-retained
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_map_entries(+,+,-)
clear_weak_map_entries(
    Garbage, [entry(Key, Value) | Tail], [entry(Key, Value) | Cleared]) :-
    list_not_member(Key, Garbage),
    structural_references(reference(Value), ValueReferences),
    lists_disjoint(ValueReferences, Garbage),
    clear_weak_map_entries(Garbage, Tail, Cleared).

% @latex equation:gc-clear-weak-payload
% @variant map-removed-key
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_map_entries(+,+,-)
clear_weak_map_entries(Garbage, [entry(Key, _Value) | Tail], Cleared) :-
    list_member(Key, Garbage),
    clear_weak_map_entries(Garbage, Tail, Cleared).

% @latex equation:gc-clear-weak-payload
% @variant map-removed-value
% @lean Newspeak.Heap.collectWeakContainer
% @mode clear_weak_map_entries(+,+,-)
clear_weak_map_entries(Garbage, [entry(Key, Value) | Tail], Cleared) :-
    list_not_member(Key, Garbage),
    structural_references(reference(Value), ValueReferences),
    lists_overlap(ValueReferences, Garbage),
    clear_weak_map_entries(Garbage, Tail, Cleared).

% @latex equation:gc-pruned-actor-heap
% @lean Newspeak.Heap.collectHeapAtReachability
% @mode gc_pruned_actor_heap(+,+,+,-)
gc_pruned_actor_heap(Heap, Garbage, Kept, Pruned) :-
    gc_application(pruned_actor_heap(Heap, Garbage, Kept, Pruned)).

% @latex equation:gc-prune-store
% @lean Newspeak.AllocationState.collectGarbage
% @mode gc_prune_store(+,+,-)
gc_prune_store(World, Garbage, Pruned) :-
    gc_application(prune_store(World, Garbage, Pruned)).

% @latex equation:gc-roots-and-successors
% @variant intersection-empty
% @lean Newspeak.FiniteStore.containsKey
% @mode list_intersection(+,+,-)
list_intersection([], _Right, []).

% @latex equation:gc-roots-and-successors
% @variant intersection-keep
% @lean Newspeak.FiniteStore.containsKey
% @mode list_intersection(+,+,-)
list_intersection([Head | Tail], Right, [Head | Result]) :-
    list_member(Head, Right),
    list_intersection(Tail, Right, Result).

% @latex equation:gc-roots-and-successors
% @variant intersection-drop
% @lean Newspeak.FiniteStore.containsKey
% @mode list_intersection(+,+,-)
list_intersection([Head | Tail], Right, Result) :-
    list_not_member(Head, Right),
    list_intersection(Tail, Right, Result).

% @latex equation:gc-clear-weak-payload
% @variant disjoint-empty
% @lean Newspeak.FiniteStore.containsKey
% @mode lists_disjoint(+,+)
lists_disjoint([], _Right).

% @latex equation:gc-clear-weak-payload
% @variant disjoint-step
% @lean Newspeak.FiniteStore.containsKey
% @mode lists_disjoint(+,+)
lists_disjoint([Head | Tail], Right) :-
    list_not_member(Head, Right),
    lists_disjoint(Tail, Right).

% @latex equation:gc-clear-weak-payload
% @variant overlap-here
% @lean Newspeak.FiniteStore.containsKey
% @mode lists_overlap(+,+)
lists_overlap([Head | _Tail], Right) :-
    list_member(Head, Right).

% @latex equation:gc-clear-weak-payload
% @variant overlap-later
% @lean Newspeak.FiniteStore.containsKey
% @mode lists_overlap(+,+)
lists_overlap([Head | Tail], Right) :-
    list_not_member(Head, Right),
    lists_overlap(Tail, Right).

% @latex equation:gc-reachability
% @variant application
% @lean Newspeak.Heap.collectHeap
% @mode gc_application(+)
gc_application(GCComputation).

% @latex equation:copy-stack-frame-segment
% @lean Newspeak.copyStackFrameSegment
% @mode copy_stack_frame_segment(+,+,+,+,-)
copy_stack_frame_segment(Stack, Start, Count, FreshKeys, Copied) :-
    list_drop_exact(Stack, Start, Suffix),
    list_take_exact(Suffix, Count, Segment),
    fresh_frame_renaming(Segment, FreshKeys, Renaming),
    rename_frame_templates(Renaming, Segment, Copied).

% @latex equation:copy-stack-frame-segment
% @variant renaming-empty
% @lean Newspeak.freshFrameRenaming
% @mode fresh_frame_renaming(+,+,-)
fresh_frame_renaming([], [], []).

% @latex equation:copy-stack-frame-segment
% @variant renaming-step
% @lean Newspeak.freshFrameRenaming
% @mode fresh_frame_renaming(+,+,-)
fresh_frame_renaming(
    [frame_template(Key, _Record, _Control) | Frames],
    [Fresh | FreshKeys],
    [pair(Key, fresh_frame(Fresh)) | Renaming]) :-
    fresh_frame_renaming(Frames, FreshKeys, Renaming).

% @latex equation:copy-stack-frame-segment
% @variant rename-empty
% @lean Newspeak.renameFrameTemplate
% @mode rename_frame_templates(+,+,-)
rename_frame_templates(_Renaming, [], []).

% @latex equation:copy-stack-frame-segment
% @variant rename-step
% @lean Newspeak.renameFrameTemplate
% @mode rename_frame_templates(+,+,-)
rename_frame_templates(Renaming, [Frame | Frames], [Renamed | RenamedFrames]) :-
    stack_materialization_application(
        rename_frame_template(Renaming, Frame, Renamed)),
    rename_frame_templates(Renaming, Frames, RenamedFrames).

% @latex equation:copy-stack-frame-segment
% @variant drop-zero
% @lean List.drop
% @mode list_drop_exact(+,+,-)
list_drop_exact(List, zero, List).

% @latex equation:copy-stack-frame-segment
% @variant drop-successor
% @lean List.drop
% @mode list_drop_exact(+,+,-)
list_drop_exact([_Head | Tail], succ(Count), Result) :-
    list_drop_exact(Tail, Count, Result).

% @latex equation:copy-stack-frame-segment
% @variant take-zero
% @lean List.take
% @mode list_take_exact(+,+,-)
list_take_exact(_List, zero, []).

% @latex equation:copy-stack-frame-segment
% @variant take-successor
% @lean List.take
% @mode list_take_exact(+,+,-)
list_take_exact([Head | Tail], succ(Count), [Head | Result]) :-
    list_take_exact(Tail, Count, Result).

% --------------------------------------------------------------------------
% Complete Newspeak PEG/action/front-end coverage
% --------------------------------------------------------------------------

% The executable Lean grammar is one finite association list.  These group
% views expose the exact entries for each displayed grammar equation without
% copying a second, potentially drifting PEG table into this file.
% @latex equation:newspeak-punctuation-peg
% @lean Newspeak.newspeakPunctuation
% @mode newspeak_punctuation_peg(+,+,-)
newspeak_punctuation_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, punctuation, Name, Body).

% @latex equation:newspeak-lexical-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_lexical_peg(+,+,-)
newspeak_lexical_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, lexical, Name, Body).

% @latex equation:newspeak-word-tokens
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_word_token_peg(+,+,-)
newspeak_word_token_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, word_tokens, Name, Body).

% @latex equation:newspeak-literal-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_literal_peg(+,+,-)
newspeak_literal_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, literals, Name, Body).

% @latex equation:newspeak-type-word-set
% @variant complete-set
% @lean Newspeak.newspeakTypeWords
% @mode newspeak_type_words(-)
newspeak_type_words([
    word_arg, word_for, word_generic, word_inherited_type_of, word_is,
    word_message, word_of, word_receiver_type, word_subtype_of,
    word_type_arg, word_where]).

% @latex equation:newspeak-type-word-set
% @variant membership
% @lean Newspeak.newspeakTypeWords
% @mode newspeak_type_word(+)
newspeak_type_word(Word) :-
    newspeak_type_words(Words),
    list_member(Word, Words).

% @latex equation:newspeak-type-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_type_peg(+,+,-)
newspeak_type_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, types, Name, Body).

% @latex equation:newspeak-type-pattern-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_type_pattern_peg(+,+,-)
newspeak_type_pattern_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, type_patterns, Name, Body).

% @latex equation:newspeak-message-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_message_peg(+,+,-)
newspeak_message_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, messages, Name, Body).

% @latex equation:newspeak-expression-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_expression_peg(+,+,-)
newspeak_expression_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, expressions, Name, Body).

% @latex equation:newspeak-declaration-peg
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_declaration_peg(+,+,-)
newspeak_declaration_peg(Classes, Name, Body) :-
    newspeak_grammar_group_entry(Classes, declarations, Name, Body).

% @latex equation:newspeak-punctuation-peg
% @variant group-entry
% @lean Newspeak.newspeakGrammarEntries
% @mode newspeak_grammar_group_entry(+,+,+,-)
newspeak_grammar_group_entry(Classes, Group, Name, Body) :-
    front_end_application(
        newspeak_grammar_group_entry(Classes, Group, Name, Body)).

% Action groups all use the single total `newspeakSurfaceAction` case split.
% @latex equation:newspeak-type-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_type_action(+,+,+,+,+,+,-)
newspeak_type_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        type_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:surface-message-folds
% @lean Newspeak.foldExplicitMessages
% @mode surface_message_fold(+,+,+,-)
surface_message_fold(Kind, Receiver, Messages, Result) :-
    front_end_application(
        surface_message_fold(Kind, Receiver, Messages, Result)).

% @latex equation:newspeak-literal-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_literal_action(+,+,+,+,+,+,-)
newspeak_literal_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        literal_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-structural-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_structural_action(+,+,+,+,+,+,-)
newspeak_structural_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        structural_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-action-sequence-helpers
% @lean Newspeak.flattenSurfaceStatements
% @mode newspeak_action_sequence_helper(+,+,-)
newspeak_action_sequence_helper(Kind, Values, Result) :-
    front_end_application(action_sequence_helper(Kind, Values, Result)).

% @latex equation:newspeak-expression-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_expression_action(+,+,+,+,+,+,-)
newspeak_expression_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        expression_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-send-fold-actions
% @lean Newspeak.foldImplicitMessages
% @mode newspeak_send_fold_action(+,+,+,+,+,+,-)
newspeak_send_fold_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        send_fold_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-compound-expression-actions
% @lean Newspeak.makeSurfaceCascade
% @mode newspeak_compound_expression_action(+,+,+,+,+,+,-)
newspeak_compound_expression_action(
    Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        compound_expression_actions,
        Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-pattern-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_pattern_action(+,+,+,+,+,+,-)
newspeak_pattern_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        pattern_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-inheritance-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_inheritance_action(+,+,+,+,+,+,-)
newspeak_inheritance_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        inheritance_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-declaration-actions
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_declaration_action(+,+,+,+,+,+,-)
newspeak_declaration_action(Decoders, Name, Start, End, Values, Slice, Result) :-
    newspeak_action_group(
        declaration_actions, Decoders, Name, Start, End, Values, Slice, Result).

% @latex equation:newspeak-type-actions
% @variant grouped-action
% @lean Newspeak.newspeakSurfaceAction
% @mode newspeak_action_group(+,+,+,+,+,+,+,-)
newspeak_action_group(
    Group, Decoders, Name, Start, End, Values, Slice, Result) :-
    front_end_application(
        newspeak_action_group(
            Group, Decoders, Name, Start, End, Values, Slice, Result)).

% Metadata association is deliberately separate from the AST action result.
% @latex equation:metadata-trivia-gap
% @lean Newspeak.SurfaceMetadata
% @mode metadata_trivia_gap(+,+,+)
metadata_trivia_gap(LeftEnd, RightStart, Gap) :-
    front_end_application(metadata_trivia_gap(LeftEnd, RightStart, Gap)).

% @latex equation:metadata-association
% @lean Newspeak.SurfaceMetadata
% @mode metadata_association(+,+,+)
metadata_association(Metadata, Nodes, Association) :-
    front_end_application(metadata_association(Metadata, Nodes, Association)).

% @latex equation:metadata-attachment
% @lean Newspeak.SurfaceMetadata
% @mode metadata_attachment(+,+,-)
metadata_attachment(Unit, Association, Attached) :-
    front_end_application(metadata_attachment(Unit, Association, Attached)).

% The elaboration and program-image equations below are graph views of the
% already executable Lean derivation functions used by `front_end_derivation`.
% @latex equation:front-end-message-template
% @lean Newspeak.elaborateMessageTemplate
% @mode front_end_message_template(+,+,+,-)
front_end_message_template(Services, Context, Clause, Template) :-
    elaborate_message_template(
        elaborate_message_template(Services, Context, Clause, Template),
        Services, Context, Clause, Template).

% @latex equation:front-end-body-descriptor
% @lean Newspeak.ClassBodyDescriptor
% @mode front_end_body_descriptor(+,+,-)
front_end_body_descriptor(Input, Context, Descriptor) :-
    front_end_application(body_descriptor(Input, Context, Descriptor)).

% @latex equation:front-end-application-identities
% @lean Newspeak.elaborationIdentitiesFrom
% @mode front_end_application_identities(+,-)
front_end_application_identities(Identification, Identities) :-
    front_end_application(application_identities(Identification, Identities)).

% @latex equation:front-end-anonymous-application-descriptor
% @lean Newspeak.deriveAnonymousApplication
% @mode front_end_anonymous_application_descriptor(+,+,+,-)
front_end_anonymous_application_descriptor(
    Config, Identification, Application, Descriptor) :-
    front_end_application(
        anonymous_application_descriptor(
            Config, Identification, Application, Descriptor)).

% @latex equation:front-end-named-application-descriptor
% @lean Newspeak.deriveCompleteClassProgram
% @mode front_end_named_application_descriptor(+,+,+,-)
front_end_named_application_descriptor(
    Config, Identification, Declaration, Descriptor) :-
    front_end_application(
        named_application_descriptor(
            Config, Identification, Declaration, Descriptor)).

% @latex equation:front-end-bodyless-prefix
% @lean Newspeak.deriveBodylessMixinChainProgram
% @mode front_end_bodyless_prefix(+,+,-)
front_end_bodyless_prefix(Context, Inheritance, Prefix) :-
    front_end_application(bodyless_prefix(Context, Inheritance, Prefix)).

% @latex equation:front-end-bodied-prefix
% @lean Newspeak.deriveCompleteClassProgram
% @mode front_end_bodied_prefix(+,+,-)
front_end_bodied_prefix(Context, Inheritance, Prefix) :-
    front_end_application(bodied_prefix(Context, Inheritance, Prefix)).

% @latex equation:derived-auxiliary-indexes
% @lean Newspeak.DerivedProgramImage
% @mode derived_auxiliary_indexes(+,-)
derived_auxiliary_indexes(Image, Indexes) :-
    front_end_application(derived_auxiliary_indexes(Image, Indexes)).

% @latex equation:static-well-formedness-components
% @lean Newspeak.ProgramDerivationServices.surfaceOK
% @mode static_well_formedness_components(+,+,-)
static_well_formedness_components(Unit, Identification, Components) :-
    front_end_application(
        static_well_formedness_components(Unit, Identification, Components)).

% @latex equation:annotated-core-roots
% @lean Newspeak.AnnotatedCoreValid
% @mode annotated_core_roots(+,+,-)
annotated_core_roots(Program, Expression, Roots) :-
    front_end_application(annotated_core_roots(Program, Expression, Roots)).

% @latex equation:annotated-program-validity
% @lean Newspeak.AnnotatedCoreValid
% @mode annotated_program_valid(+,+,+)
annotated_program_valid(Program, Expression, Fuel) :-
    annotated_core_valid(
        annotated_core_valid(Program, Expression, Fuel),
        Program, Expression, Fuel).

% @latex equation:compilation-unit-projection
% @lean Newspeak.PEGParsesNewspeakUnit
% @mode compilation_unit_projection(+,+,+,-,-)
compilation_unit_projection(Grammar, Decoders, Source, Unit, Metadata) :-
    peg_parses_newspeak_unit(
        peg_parses_newspeak_unit(Grammar, Decoders, Source, Unit, Metadata),
        Grammar, Decoders, Source, Unit, Metadata).

% @latex equation:front-end-reflective-change
% @lean Newspeak.identifiedSourceReflectionFrontEnd
% @mode front_end_reflective_change(+,+,+,-)
front_end_reflective_change(Source, Commands, PreviousProgram, Result) :-
    front_end_application(
        front_end_reflective_change(
            Source, Commands, PreviousProgram, Result)).

% @latex equation:compilation-unit-projection
% @variant application
% @lean Newspeak.FrontEndDerivation
% @mode front_end_application(+)
front_end_application(FrontEndComputation).

% @latex equation:prepare-reflection
% @variant patch-source-application
% @lean Newspeak.ReflectionFrontEnd.patchSourceCommands
% @mode patch_source_commands_application(+,+,+,+,+)
patch_source_commands_application(
    patch_source_commands(FrontEnd, Source, Commands, Candidate),
    FrontEnd, Source, Commands, Candidate).

% @latex equation:prepare-reflection
% @variant reelaborate-application
% @lean Newspeak.ReflectionFrontEnd.reelaborateProgram
% @mode reelaborate_program_application(+,+,+,+,+)
reelaborate_program_application(
    reelaborate_program(FrontEnd, OldProgram, Source, Program),
    FrontEnd, OldProgram, Source, Program).

% @latex equation:prepare-reflection
% @variant runtime-application
% @lean Newspeak.ReflectionRuntimePreparation
% @mode prepare_reflection_runtime_application(+,+,+,+,+,+,+)
prepare_reflection_runtime_application(
    prepare_reflection_runtime(
        PrepareRuntime, Program, Requester, Transaction, Before, Candidate),
    PrepareRuntime, Program, Requester, Transaction, Before, Candidate).

% @latex equation:prepare-reflection
% @lean Newspeak.PrologBridge.PrologPrepareReflection.prepared
% @mode prepare_reflection(+,+,+,+,+,-)
prepare_reflection(
    FrontEnd, PrepareRuntime, reflective_vm(Source, Before), Requester,
    Transaction, reflective_vm(SourceCandidate, Committed)) :-
    filter_reflection_commands(Transaction, code, CodeCommands),
    patch_source_commands_application(
        patch_source_commands(
            FrontEnd, Source, CodeCommands, SourceCandidate),
        FrontEnd, Source, CodeCommands, SourceCandidate),
    actor_world_program(Before, OldProgram),
    reelaborate_program_application(
        reelaborate_program(
            FrontEnd, OldProgram, SourceCandidate, ProgramCandidate),
        FrontEnd, OldProgram, SourceCandidate, ProgramCandidate),
    prepare_reflection_runtime_application(
        prepare_reflection_runtime(
            PrepareRuntime, ProgramCandidate, Requester, Transaction,
            Before, RuntimeCandidate),
        PrepareRuntime, ProgramCandidate, Requester, Transaction,
        Before, RuntimeCandidate),
    actor_world_install_field(
        RuntimeCandidate, program, ProgramCandidate, WithProgram),
    actor_world_field(Before, program_version, Version),
    actor_world_install_field(
        WithProgram, program_version, succ(Version), Committed).
% @latex equation:reflection-validity
% @variant validity-witness
% @lean Newspeak.ValidReflection
% @mode valid_reflection(+,+,+,+,+,+,+,+)
valid_reflection(
    valid_reflection(
        FrontEnd, PrepareRuntime, Validate, Before, Requester, Transaction,
        After),
    FrontEnd, PrepareRuntime, Validate, Before, Requester, Transaction, After).

% @latex equation:reflection-failure
% @variant rejection-witness
% @lean Newspeak.ReflectionRejected
% @mode reflection_rejected(+,+,+,+,+,+)
reflection_rejected(
    reflection_rejected(State, Requester, Transaction, Failure),
    _Rejected, State, Requester, Transaction, Failure).

% @latex rule:Reflection-Commit
% @lean Newspeak.ReflectionStep.commit
% @mode reflection_step(+,+,+,+,+,-)
reflection_step(
    FrontEnd, PrepareRuntime, Validate, _Rejected, Before, After) :-
    valid_reflection(
        valid_reflection(
            FrontEnd, PrepareRuntime, Validate, Before, _Requester,
            _Transaction, After),
        FrontEnd, PrepareRuntime, Validate, Before, _Requester, _Transaction,
        After).

% @latex rule:Reflection-Reject
% @lean Newspeak.ReflectionStep.reject
% @mode reflection_step(+,+,+,+,+,-)
reflection_step(
    _FrontEnd, _PrepareRuntime, _Validate, Rejected, State, State) :-
    reflection_rejected(
        reflection_rejected(
            State, _Requester, _Transaction, _Failure),
        Rejected, State, _Requester, _Transaction, _Failure).

% @latex equation:reflective-step
% @lean Newspeak.PrologBridge.PrologReflectionStep
% @mode reflective_step(+,+,+,+,+,-)
reflective_step(
    FrontEnd, PrepareRuntime, Validate, Rejected, Before, After) :-
    reflection_step(
        FrontEnd, PrepareRuntime, Validate, Rejected, Before, After).

% @latex equation:remote-debugger-component-step
% @lean Newspeak.VMReflectionStep.selected
% @mode vm_reflection_step(+,+,+,+,+,+,-)
vm_reflection_step(
    FrontEnd, PrepareRuntime, Validate, Rejected, BeforeNetwork, VM,
    AfterNetwork) :-
    store_lookup(BeforeNetwork, VM, some(LocalBefore)),
    reflection_step(
        FrontEnd, PrepareRuntime, Validate, Rejected, LocalBefore,
        LocalAfter),
    store_install(BeforeNetwork, VM, LocalAfter, AfterNetwork).

% The occurrence premise is universal over the VM's component stores and is
% carried explicitly; the containment derivation itself is expanded below.
% @latex equation:mirror-target-containment
% @variant occurs-witness
% @lean Newspeak.MirrorTargetOccurs
% @mode mirror_target_occurs(+,+,+)
mirror_target_occurs(
    mirror_target_occurs(World, Target), World, Target).

% @latex equation:mirror-target-containment
% @variant world-heap-shared
% @lean Newspeak.ActorWorldHeap.shared
% @mode actor_world_heap(+,+,+)
actor_world_heap(world_heap_shared(World), World, Heap) :-
    actor_world_field(World, value_heap, Heap).

% @latex equation:mirror-target-containment
% @variant world-heap-private
% @lean Newspeak.ActorWorldHeap.privateHeap
% @mode actor_world_heap(+,+,+)
actor_world_heap(world_heap_private(World, Actor), World, Heap) :-
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, Heap).

% @latex equation:mirror-target-containment
% @variant parent-cohort
% @lean Newspeak.PrologBridge.PrologMirrorTargetParent.cohort
% @mode mirror_target_parent(+,+,+,+)
mirror_target_parent(parent_cohort(Occurs), World, Target, vm_target(VM)) :-
    actor_world_field(World, vm, VM),
    dif(Target, vm_target(VM)),
    mirror_target_occurs(Occurs, World, Target).

% @latex equation:mirror-target-containment
% @variant parent-mixin-program
% @lean Newspeak.PrologBridge.PrologMirrorTargetParent.mixinProgram
% @mode mirror_target_parent(+,+,+,+)
mirror_target_parent(parent_mixin_program(Mixin), _World,
                     mixin_target(Mixin), program_target).

% @latex equation:mirror-target-containment
% @variant parent-method-mixin
% @lean Newspeak.PrologBridge.PrologMirrorTargetParent.methodMixin
% @mode mirror_target_parent(+,+,+,+)
mirror_target_parent(parent_method_mixin(Method, Mixin), World,
                     method_target(Method), mixin_target(Mixin)) :-
    actor_world_program(World, Program),
    program_method_owner(Program, Method, Mixin).

% @latex equation:mirror-target-containment
% @variant parent-class-mixin
% @lean Newspeak.PrologBridge.PrologMirrorTargetParent.classMixin
% @mode mirror_target_parent(+,+,+,+)
mirror_target_parent(parent_class_mixin(HeapProof, Class), World,
                     class_target(Class), mixin_target(Mixin)) :-
    actor_world_heap(HeapProof, World, Heap),
    heap_classes(Heap, Classes),
    store_lookup(
        Classes, Class,
        some(class_def(Mixin, _Superclass, _EnclosingObject,
                       _Metaclass, _Origin, _Factory))).

% @latex equation:mirror-target-containment
% @variant parent-object-class
% @lean Newspeak.PrologBridge.PrologMirrorTargetParent.objectClass
% @mode mirror_target_parent(+,+,+,+)
mirror_target_parent(parent_object_class(HeapProof, Object), World,
                     object_target(Object), class_target(Class)) :-
    actor_world_heap(HeapProof, World, Heap),
    class_of(Heap, Object, some(Class)).

% @latex equation:mirror-target-containment
% @variant parent-activation-object
% @lean Newspeak.PrologBridge.PrologMirrorTargetParent.activationObject
% @mode mirror_target_parent(+,+,+,+)
mirror_target_parent(parent_activation_object(HeapProof, Activation), World,
                     activation_target(Activation), object_target(Object)) :-
    actor_world_heap(HeapProof, World, Heap),
    activation_at(Heap, Activation, some(Definition)),
    activation_receiver(Definition, Object).

% @latex equation:mirror-target-containment
% @variant reflexive
% @lean Newspeak.PrologBridge.PrologMirrorTargetContained.refl
% @mode mirror_target_contained(+,+,+,+)
mirror_target_contained(contained_reflexive(Target), _World, Target, Target).

% @latex equation:mirror-target-containment
% @variant parent-transitive
% @lean Newspeak.PrologBridge.PrologMirrorTargetContained.parent
% @mode mirror_target_contained(+,+,+,+)
mirror_target_contained(contained_parent(EdgeProof, TailProof), World,
                        Child, Ancestor) :-
    mirror_target_parent(EdgeProof, World, Child, Parent),
    mirror_target_contained(TailProof, World, Parent, Ancestor).

% @latex rule:Mirror-Derive
% @variant allocation-mirror
% @lean Newspeak.PrologBridge.allocateAuthorityMirror
% @mode allocate_authority_mirror(+,+,+,-,-)
allocate_authority_mirror(
    allocation_state(
        Heap, NextMirror, NextActivation, NextClosure, NextObject, NextClass),
    Class, Authority,
    allocation_state(
        NewHeap, succ(NextMirror), NextActivation, NextClosure, NextObject,
        NextClass),
    mirror_id(NextMirror)) :-
    heap_install_mirror(
        Heap, mirror_id(NextMirror),
        mirror_def(Class, authority_payload(Authority)), NewHeap).

% @latex rule:Mirror-Derive
% @variant config-allocation
% @lean Newspeak.SequentialConfig.allocation
% @mode replace_config_allocation(+,+,-)
replace_config_allocation(
    sequential_config(_OldAllocation, Stack, Control), Allocation,
    sequential_config(Allocation, Stack, Control)).

% @latex rule:Mirror-Derive
% @variant replace-absent
% @lean Newspeak.ActorWorld.replaceActorAllocationCoherently
% @mode replace_actor_allocation_coherently(+,+,+,-)
replace_actor_allocation_coherently(World, Actor, Allocation, FinalWorld) :-
    actor_run_state(World, Actor, none),
    actor_world_field(World, actor_allocations, Allocations),
    store_install(Allocations, Actor, Allocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, FinalWorld).

% @latex rule:Mirror-Derive
% @variant replace-idle
% @lean Newspeak.ActorWorld.replaceActorAllocationCoherently
% @mode replace_actor_allocation_coherently(+,+,+,-)
replace_actor_allocation_coherently(World, Actor, Allocation, FinalWorld) :-
    actor_run_state(World, Actor, some(idle)),
    actor_world_field(World, actor_allocations, Allocations),
    store_install(Allocations, Actor, Allocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, FinalWorld).

% @latex rule:Mirror-Derive
% @variant replace-running
% @lean Newspeak.ActorWorld.replaceActorAllocationCoherently
% @mode replace_actor_allocation_coherently(+,+,+,-)
replace_actor_allocation_coherently(World, Actor, Allocation, FinalWorld) :-
    actor_run_state(
        World, Actor,
        some(running_turn(Configuration, ReplyPromise, TriggeringEvent))),
    replace_config_allocation(Configuration, Allocation, NewConfiguration),
    actor_world_field(World, actor_allocations, Allocations),
    store_install(Allocations, Actor, Allocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, WithAllocation),
    actor_world_field(WithAllocation, run_states, RunStates),
    store_install(
        RunStates, Actor,
        running_turn(NewConfiguration, ReplyPromise, TriggeringEvent),
        NewRunStates),
    actor_world_install_field(
        WithAllocation, run_states, NewRunStates, FinalWorld).

% @latex rule:Mirror-Derive
% @variant replace-paused
% @lean Newspeak.ActorWorld.replaceActorAllocationCoherently
% @mode replace_actor_allocation_coherently(+,+,+,-)
replace_actor_allocation_coherently(World, Actor, Allocation, FinalWorld) :-
    actor_run_state(
        World, Actor,
        some(paused_turn(
            Configuration, ReplyPromise, TriggeringEvent, PauseToken,
            StopReason))),
    replace_config_allocation(Configuration, Allocation, NewConfiguration),
    actor_world_field(World, actor_allocations, Allocations),
    store_install(Allocations, Actor, Allocation, NewAllocations),
    actor_world_install_field(
        World, actor_allocations, NewAllocations, WithAllocation),
    actor_world_field(WithAllocation, run_states, RunStates),
    store_install(
        RunStates, Actor,
        paused_turn(
            NewConfiguration, ReplyPromise, TriggeringEvent, PauseToken,
            StopReason),
        NewRunStates),
    actor_world_install_field(
        WithAllocation, run_states, NewRunStates, FinalWorld).

% @latex rule:Mirror-Derive
% @lean Newspeak.PrologBridge.MirrorDerivationStep.derive
% @mode mirror_derivation_step(+,+,+,+,+,-,-)
mirror_derivation_step(
    World, Actor, Mirror, Target, NewRights, After, NewMirror) :-
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, Heap),
    heap_mirrors(Heap, Mirrors),
    store_lookup(
        Mirrors, Mirror,
        some(mirror_def(
            Class,
            authority_payload(
                mirror_authority(VM, ParentTarget, ParentRights))))),
    actor_world_field(World, vm, VM),
    list_member(delegate_right, ParentRights),
    mirror_target_contained(
        _ContainmentProof, World, Target, ParentTarget),
    list_subset(NewRights, ParentRights),
    allocate_authority_mirror(
        Allocation, Class,
        mirror_authority(VM, Target, NewRights), NewAllocation, NewMirror),
    replace_actor_allocation_coherently(
        World, Actor, NewAllocation, After).

% @latex rule:VM-Primitive
% @variant host-primitive-witness
% @lean Newspeak.PrologBridge.HostPrimitiveRelation
% @mode host_primitive_application(+,+,+,+,-,-)
host_primitive_application(
    host_primitive(World, Selector, Arguments, After, Value),
    World, Selector, Arguments, After, Value).

% @latex rule:VM-Primitive
% @lean Newspeak.PrologBridge.VMPrimitiveInvocation.invoke
% @mode vm_primitive_invocation(+,+,+,+,+,+,-,-)
vm_primitive_invocation(
    HostPrimitive, World, Actor, Mirror, Selector, Arguments, After, Value) :-
    actor_allocation(World, Actor, some(Allocation)),
    allocation_state_heap(Allocation, Heap),
    heap_mirrors(Heap, Mirrors),
    actor_world_field(World, vm, VM),
    store_lookup(
        Mirrors, Mirror,
        some(mirror_def(
            _Class,
            authority_payload(
                mirror_authority(VM, vm_target(VM), Rights))))),
    list_member(primitive_right, Rights),
    host_primitive_application(
        HostPrimitive, World, Selector, Arguments, After, Value).

% --------------------------------------------------------------------------
% Optional global garbage-collection wrapper
% --------------------------------------------------------------------------

% @latex rule:GC-Lift
% @variant underlying-witness
% @lean Newspeak.GCUnderlyingTransition
% @mode gc_underlying_application(+,+,+,+,+)
gc_underlying_application(
    underlying_transition(Label, Before, After),
    _Underlying, Label, Before, After).

% @latex equation:gc-new-identities
% @variant projection-witness
% @lean Newspeak.PrologBridge.PrologGCLiftStep
% @mode gc_new_references_application(+,+,+,+,-)
gc_new_references_application(
    new_references(Before, After, References),
    _NewReferences, Before, After, References).

% @latex rule:GC-Lift
% @variant fresh-empty
% @lean Newspeak.GCNewReferencesFresh
% @mode gc_new_references_fresh(+,+)
gc_new_references_fresh([], _Allocated).

% @latex rule:GC-Lift
% @variant fresh-cons
% @lean Newspeak.GCNewReferencesFresh
% @mode gc_new_references_fresh(+,+)
gc_new_references_fresh([Reference|Remaining], Allocated) :-
    list_not_member(Reference, Allocated),
    gc_new_references_fresh(Remaining, Allocated).

% @latex rule:GC-Lift
% @variant extend-identities
% @lean Newspeak.extendAllocatedReferences
% @mode extend_allocated_references(+,+,-)
extend_allocated_references(Allocated, NewReferences, Extended) :-
    list_append(Allocated, NewReferences, Combined),
    list_deduplicated(Combined, Extended).

% @latex rule:GC-Lift
% @lean Newspeak.PrologBridge.PrologGCLiftStep.lift
% @mode gc_lift_step(+,+,+,+,-)
gc_lift_step(
    Underlying, NewReferences, Label,
    gc_wrapped_world(BeforeWorld, Allocated),
    gc_wrapped_world(AfterWorld, Extended)) :-
    gc_underlying_application(
        underlying_transition(Label, BeforeWorld, AfterWorld),
        Underlying, Label, BeforeWorld, AfterWorld),
    gc_new_references_application(
        new_references(BeforeWorld, AfterWorld, FreshReferences),
        NewReferences, BeforeWorld, AfterWorld, FreshReferences),
    gc_new_references_fresh(FreshReferences, Allocated),
    extend_allocated_references(
        Allocated, FreshReferences, Extended).

% @latex equation:admissible-garbage-set
% @variant admissibility-witness
% @lean Newspeak.GCAdmissibility
% @mode gc_admissible_application(+,+,+,+,+)
gc_admissible_application(
    admissible_gc(World, Roots, Garbage),
    _Admissible, World, Roots, Garbage).

% @latex rule:GC-Collect
% @variant prune-witness
% @lean Newspeak.GCPruning
% @mode gc_prune_application(+,+,+,+,-)
gc_prune_application(
    prune_gc(World, Garbage, After), _Prune, World, Garbage, After).

% @latex rule:GC-Collect
% @lean Newspeak.PrologBridge.PrologGCCollectStep.collect
% @mode gc_collect_step(+,+,+,+,-)
gc_collect_step(
    Admissible, Prune, Roots,
    gc_wrapped_world(World, Allocated),
    gc_wrapped_world(After, Allocated)) :-
    gc_admissible_application(
        admissible_gc(World, Roots, Garbage),
        Admissible, World, Roots, Garbage),
    gc_prune_application(
        prune_gc(World, Garbage, After), Prune, World, Garbage, After).

% --------------------------------------------------------------------------
% Local and non-local return
% --------------------------------------------------------------------------

% @latex equation:return-target
% @lean Newspeak.ActivationDef.provenance
% @mode activation_provenance(+,-)
activation_provenance(
    activation_def(_Class, Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Provenance).

% @latex equation:return-target
% @lean Newspeak.ActivationDef.homeMethod
% @mode activation_home_method(+,-)
activation_home_method(
    activation_def(_Class, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, Home,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Home).

% @latex rule:Return-Cannot
% @lean Newspeak.ActivationDef.continuable
% @mode activation_continuable(+,-)
activation_continuable(
    activation_def(_Class, _Provenance, _Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Continuable).

% @latex equation:return-target
% @variant absent
% @lean Newspeak.Heap.returnTarget
% @mode return_target(+,+,-)
return_target(Heap, Current, none) :-
    activation_at(Heap, Current, none).

% @latex equation:return-target
% @variant top
% @lean Newspeak.Heap.returnTarget
% @mode return_target(+,+,-)
return_target(Heap, Current, none) :-
    activation_at(Heap, Current, some(Activation)),
    activation_provenance(Activation, top_provenance).

% @latex equation:return-target
% @variant method
% @lean Newspeak.Heap.returnTarget
% @mode return_target(+,+,-)
return_target(Heap, Current, some(Current)) :-
    activation_at(Heap, Current, some(Activation)),
    activation_provenance(Activation, method_provenance(_Method)).

% @latex equation:return-target
% @variant closure
% @lean Newspeak.Heap.returnTarget
% @mode return_target(+,+,-)
return_target(Heap, Current, Target) :-
    activation_at(Heap, Current, some(Activation)),
    activation_provenance(
        Activation, closure_provenance(_Declaration)),
    activation_home_method(Activation, Target).

% @latex equation:return-target
% @variant initializer
% @lean Newspeak.Heap.returnTarget
% @mode return_target(+,+,-)
return_target(Heap, Current, some(Current)) :-
    activation_at(Heap, Current, some(Activation)),
    activation_provenance(
        Activation, initializer_provenance(_Declaration)).

% @latex equation:dependents
% @variant target
% @lean Newspeak.DependentActivation.target
% @mode dependent_activation(+,+,+)
dependent_activation(_Heap, Target, Target).

% @latex equation:dependents
% @variant child
% @lean Newspeak.DependentActivation.child
% @mode dependent_activation(+,+,+)
dependent_activation(Heap, Target, Child) :-
    dependent_activation(Heap, Target, Parent),
    activation_at(Heap, Child, some(Activation)),
    activation_continuation(Activation, some(Parent)).

% @latex equation:mark-uncontinuable
% @variant activation-update
% @lean Newspeak.markActivationUncontinuable
% @mode mark_activation_uncontinuable(+,-)
mark_activation_uncontinuable(
    activation_def(Class, Provenance, Parameters, Locals,
                   Receiver, CurrentClass, _Continuation, Home,
                   _Continuable, ActivationScopes, ObjectLiteralScopes),
    activation_def(Class, Provenance, Parameters, Locals,
                   Receiver, CurrentClass, none, Home,
                   false, ActivationScopes, ObjectLiteralScopes)).

% `marked_uncontinuable(Heap, Target)` is the first-order term denoting the
% pointwise heap update in Equation (mark-uncontinuable).  Its membership is
% exposed independently by `dependent_activation/3`; the Lean bridge gives
% this constructor its exact functional interpretation.
% @latex equation:mark-uncontinuable
% @variant heap-update
% @lean Newspeak.Heap.markUncontinuable
% @mode mark_uncontinuable_heap(+,+,-)
mark_uncontinuable_heap(
    Heap, Target, marked_uncontinuable(Heap, Target)).

% @latex rule:Return-Value
% @lean Newspeak.Program.returnMachineNext
% @mode return_machine_step(+,+,-)
return_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current, eval_stack_push(Frames, return_frame))),
        object(Value)),
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        transfer(Target, Value))) :-
    return_target(Heap, Current, some(Target)).

% @latex rule:Return-Transfer
% @lean Newspeak.Program.returnMachineNext
% @mode return_machine_step(+,+,-)
return_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        transfer(Target, Value)),
    sequential_config(
        allocation_state(
            MarkedHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        Resumed,
        object(Value))) :-
    return_target(Heap, Current, some(Target)),
    activation_at(Heap, Target, some(TargetActivation)),
    activation_continuable(TargetActivation, true),
    activation_continuation(TargetActivation, some(Continuation)),
    mark_uncontinuable_heap(Heap, Target, MarkedHeap),
    resume_activation(
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        Continuation, some(Resumed)).

% @latex rule:Return-Cannot
% @variant no-continuation
% @lean Newspeak.Program.returnMachineNext
% @mode return_machine_step(+,+,-)
return_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        transfer(Target, _Value)),
    sequential_config(
        allocation_state(
            MarkedHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        throw(cannot_return))) :-
    return_target(Heap, Current, some(Target)),
    activation_at(Heap, Target, some(TargetActivation)),
    activation_continuable(TargetActivation, true),
    activation_continuation(TargetActivation, none),
    mark_uncontinuable_heap(Heap, Target, MarkedHeap).

% @latex rule:Return-Cannot
% @variant already-uncontinuable
% @lean Newspeak.Program.returnMachineNext
% @mode return_machine_step(+,+,-)
return_machine_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        transfer(Target, _Value)),
    sequential_config(
        allocation_state(
            MarkedHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        throw(cannot_return))) :-
    return_target(Heap, Current, some(Target)),
    activation_at(Heap, Target, some(TargetActivation)),
    activation_continuable(TargetActivation, false),
    mark_uncontinuable_heap(Heap, Target, MarkedHeap).

% --------------------------------------------------------------------------
% Instance-slot group initialization
% --------------------------------------------------------------------------

% @latex equation:init-sequential
% @variant immutable
% @lean Newspeak.eagerSlotInitializer
% @mode eager_slot_initializer(+,-)
eager_slot_initializer(
    immutable_slot(Slot, Initializer, Thunk),
    some(triple(Slot, Initializer, Thunk))).

% @latex equation:init-sequential
% @variant mutable-initialized
% @lean Newspeak.eagerSlotInitializer
% @mode eager_slot_initializer(+,-)
eager_slot_initializer(
    mutable_initialized_slot(Slot, Initializer, Thunk),
    some(triple(Slot, Initializer, Thunk))).

% @latex equation:init-sequential
% @variant mutable-uninitialized
% @lean Newspeak.eagerSlotInitializer
% @mode eager_slot_initializer(+,-)
eager_slot_initializer(mutable_uninitialized_slot(_Slot), none).

% @latex equation:simultaneous-expansion
% @variant install-immutable
% @lean Newspeak.Program.slotFutureInstallExpression
% @mode slot_future_install_expression(+,+,+,+,+,-)
slot_future_install_expression(
    Program, Activation, Object, Application,
    immutable_slot(Slot, _Initializer, Thunk),
    some(write_slot(
        Object, slot_address(Application, Slot),
        ordinary_send(
            PastFuture, selector('computing:'),
            [closure_literal(Thunk)])))) :-
    program_past_future_expression(Program, Activation, PastFuture).

% @latex equation:simultaneous-expansion
% @variant install-mutable
% @lean Newspeak.Program.slotFutureInstallExpression
% @mode slot_future_install_expression(+,+,+,+,+,-)
slot_future_install_expression(
    Program, Activation, Object, Application,
    mutable_initialized_slot(Slot, _Initializer, Thunk),
    some(write_slot(
        Object, slot_address(Application, Slot),
        ordinary_send(
            PastFuture, selector('computing:'),
            [closure_literal(Thunk)])))) :-
    program_past_future_expression(Program, Activation, PastFuture).

% @latex equation:simultaneous-expansion
% @variant install-uninitialized
% @lean Newspeak.Program.slotFutureInstallExpression
% @mode slot_future_install_expression(+,+,+,+,+,-)
slot_future_install_expression(
    _Program, _Activation, _Object, _Application,
    mutable_uninitialized_slot(_Slot), none).

% @latex equation:simultaneous-expansion
% @variant resolve-immutable
% @lean Newspeak.slotFutureResolveExpression
% @mode slot_future_resolve_expression(+,+,+,-)
slot_future_resolve_expression(
    Object, Application, immutable_slot(Slot, _Initializer, _Thunk),
    some(ordinary_send(
        read_slot(Object, slot_address(Application, Slot)), selector(resolve), []))).

% @latex equation:simultaneous-expansion
% @variant resolve-mutable
% @lean Newspeak.slotFutureResolveExpression
% @mode slot_future_resolve_expression(+,+,+,-)
slot_future_resolve_expression(
    Object, Application, mutable_initialized_slot(Slot, _Initializer, _Thunk),
    some(ordinary_send(
        read_slot(Object, slot_address(Application, Slot)), selector(resolve), []))).

% @latex equation:simultaneous-expansion
% @variant resolve-uninitialized
% @lean Newspeak.slotFutureResolveExpression
% @mode slot_future_resolve_expression(+,+,+,-)
slot_future_resolve_expression(
    _Object, _Application, mutable_uninitialized_slot(_Slot), none).

% @latex equation:simultaneous-expansion
% @variant installations-empty
% @lean Newspeak.PrologBridge.PrologSlotFutureInstallExpressions.nil
% @mode slot_future_install_expressions(+,+,+,+,+,-)
slot_future_install_expressions(
    _Program, _Activation, _Object, _Application, [], []).

% @latex equation:simultaneous-expansion
% @variant installations-keep
% @lean Newspeak.PrologBridge.PrologSlotFutureInstallExpressions.keep
% @mode slot_future_install_expressions(+,+,+,+,+,-)
slot_future_install_expressions(
    Program, Activation, Object, Application, [Declaration|Declarations],
    [Expression|Expressions]) :-
    slot_future_install_expression(
        Program, Activation, Object, Application, Declaration, some(Expression)),
    slot_future_install_expressions(
        Program, Activation, Object, Application, Declarations, Expressions).

% @latex equation:simultaneous-expansion
% @variant installations-skip
% @lean Newspeak.PrologBridge.PrologSlotFutureInstallExpressions.skip
% @mode slot_future_install_expressions(+,+,+,+,+,-)
slot_future_install_expressions(
    Program, Activation, Object, Application, [Declaration|Declarations], Expressions) :-
    slot_future_install_expression(
        Program, Activation, Object, Application, Declaration, none),
    slot_future_install_expressions(
        Program, Activation, Object, Application, Declarations, Expressions).

% @latex equation:simultaneous-expansion
% @variant resolutions-empty
% @lean Newspeak.PrologBridge.PrologSlotFutureResolveExpressions.nil
% @mode slot_future_resolve_expressions(+,+,+,-)
slot_future_resolve_expressions(_Object, _Application, [], []).

% @latex equation:simultaneous-expansion
% @variant resolutions-keep
% @lean Newspeak.PrologBridge.PrologSlotFutureResolveExpressions.keep
% @mode slot_future_resolve_expressions(+,+,+,-)
slot_future_resolve_expressions(
    Object, Application, [Declaration|Declarations], [Expression|Expressions]) :-
    slot_future_resolve_expression(
        Object, Application, Declaration, some(Expression)),
    slot_future_resolve_expressions(Object, Application, Declarations, Expressions).

% @latex equation:simultaneous-expansion
% @variant resolutions-skip
% @lean Newspeak.PrologBridge.PrologSlotFutureResolveExpressions.skip
% @mode slot_future_resolve_expressions(+,+,+,-)
slot_future_resolve_expressions(Object, Application, [Declaration|Declarations], Expressions) :-
    slot_future_resolve_expression(Object, Application, Declaration, none),
    slot_future_resolve_expressions(Object, Application, Declarations, Expressions).

% @latex equation:simultaneous-expansion
% @lean Newspeak.Program.slotSimCode
% @mode slot_sim_code(+,+,+,+,+,-)
slot_sim_code(Program, Activation, Object, Application, Declarations, Code) :-
    slot_future_install_expressions(
        Program, Activation, Object, Application, Declarations, Installations),
    slot_future_resolve_expressions(Object, Application, Declarations, Resolutions),
    list_append(Installations, Resolutions, Code).

% @latex equation:init-group-simultaneous
% @variant empty
% @lean Newspeak.Program.startSimultaneousSlots
% @mode start_simultaneous_slots(+,+,+,+,+,+,+,+,+,-)
start_simultaneous_slots(
    Program, State, Rest, Current, Frames, Object, Application, Declarations,
    pair(RemainingGroups, Body),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(Object, RemainingGroups, Body))) :-
    slot_sim_code(Program, Current, Object, Application, Declarations, []).

% @latex equation:init-group-simultaneous
% @variant nonempty
% @lean Newspeak.Program.startSimultaneousSlots
% @mode start_simultaneous_slots(+,+,+,+,+,+,+,+,+,-)
start_simultaneous_slots(
    Program, State, Rest, Current, Frames, Object, Application, Declarations,
    pair(RemainingGroups, Body),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_slots(
                        Later, Object, RemainingGroups, Body)))),
        evaluate(First))) :-
    slot_sim_code(
        Program, Current, Object, Application, Declarations, [First|Later]).

% @latex equation:init-groups-empty
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(Object, [], Body)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        body(method_body(ordinary_object(Object)), Body))).

% @latex equation:init-group-sequential
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(
            Object, [sequential_slot_group(Declarations)|Remaining], Body)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_sequential_slots(
            Object, Declarations, Remaining, Body))).

% @latex equation:init-group-simultaneous
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(
            Object, [simultaneous_slot_group(Declarations)|Remaining], Body)),
    After) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_current_class(Activation, some(Application)),
    start_simultaneous_slots(
        Program, State, Rest, Current, Frames, Object, Application, Declarations,
        pair(Remaining, Body), After).

% @latex equation:init-sequential
% @variant empty
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_sequential_slots(Object, [], Remaining, Body)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(Object, Remaining, Body))).

% @latex equation:init-sequential
% @variant uninitialized
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_sequential_slots(
            Object, [mutable_uninitialized_slot(_Slot)|Later],
            Remaining, Body)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_sequential_slots(Object, Later, Remaining, Body))).

% @latex equation:init-sequential
% @variant eager
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_sequential_slots(
            Object, [Declaration|Later], Remaining, Body)),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    store_initialized_slot(
                        Object, slot_address(Application, Slot), Later, Remaining, Body)))),
        evaluate(Initializer))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_current_class(Activation, some(Application)),
    eager_slot_initializer(
        Declaration, some(triple(Slot, Initializer, _Thunk))).

% @latex equation:init-sequential
% @variant store
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    store_initialized_slot(
                        Object, Slot, Later, Remaining, Body)))),
        object(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_sequential_slots(Object, Later, Remaining, Body))) :-
    write_object_slot_heap(Heap, Object, Slot, Value, NewHeap).

% @latex equation:internal-sequence
% @variant continuation-empty
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_slots([], Object, Remaining, Body)))),
        object(_Value)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(Object, Remaining, Body))).

% @latex equation:internal-sequence
% @variant continuation-next
% @lean Newspeak.Program.slotInitializationNext
% @mode slot_initialization_step(+,+,-)
slot_initialization_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_slots(
                        [First|Later], Object, Remaining, Body)))),
        object(_Value)),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    simultaneous_slots(
                        Later, Object, Remaining, Body)))),
        evaluate(First))).

% --------------------------------------------------------------------------
% Primary-factory instance allocation
% --------------------------------------------------------------------------

% @latex equation:instance-initializer-activation
% @lean Newspeak.ActivationDef.parameters
% @mode activation_parameters(+,-)
activation_parameters(
    activation_def(_Class, _Provenance, Parameters, _Locals,
                   _Receiver, _CurrentClass, _Continuation, _Home,
                   _Continuable, _ActivationScopes, _ObjectLiteralScopes),
    Parameters).

% @latex rule:Factory-New
% @variant parameters-empty
% @lean Newspeak.Program.activationParameterValues
% @mode activation_parameter_values(+,+,-)
activation_parameter_values(_Activation, [], []).

% @latex rule:Factory-New
% @variant parameters-cons
% @lean Newspeak.Program.activationParameterValues
% @mode activation_parameter_values(+,+,-)
activation_parameter_values(
    Activation, [Parameter|Parameters], [Value|Values]) :-
    activation_parameters(Activation, ParameterStore),
    store_lookup(ParameterStore, Parameter, some(Value)),
    activation_parameter_values(Activation, Parameters, Values).

% @latex rule:Factory-New
% @lean Newspeak.ClassDef.primaryFactory
% @mode class_primary_factory(+,-)
class_primary_factory(
    class_def(_Mixin, _Superclass, _EnclosingObject, _Metaclass,
              _Origin, Factory),
    Factory).

% @latex rule:Factory-New
% @lean Newspeak.FactoryDef.selector
% @mode factory_selector(+,-)
factory_selector(
    factory_def(_ActivationDeclaration, Selector, _Parameters, _Plan),
    Selector).

% @latex rule:Factory-New
% @lean Newspeak.FactoryDef.parameters
% @mode factory_parameters(+,-)
factory_parameters(
    factory_def(_ActivationDeclaration, _Selector, Parameters, _Plan),
    Parameters).

% @latex equation:instance-initializer-activation
% @lean Newspeak.FactoryDef.activationDeclaration
% @mode factory_activation_declaration(+,-)
factory_activation_declaration(
    factory_def(ActivationDeclaration, _Selector, _Parameters, _Plan),
    ActivationDeclaration).

% @latex equation:primary-factory-body
% @lean Newspeak.primaryFactoryBody
% @mode primary_factory_body(+,+,-)
primary_factory_body(
    Selector, Parameters,
    [return_statement(new_instance_current(Selector, Parameters))]).

% @latex equation:own-slots
% @lean Newspeak.MixinDef.ownSlots
% @mode mixin_own_slots(+,-)
mixin_own_slots(
    mixin_def(_Declaration, _Methods, OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, _InitializerSelector,
              _InitializerParameters, _InitializerGroups, _InitializerBody),
    OwnSlots).

% @latex equation:slot-layout
% @lean Newspeak.ClassDef.mixin
% @mode class_mixin(+,-)
class_mixin(
    class_def(Mixin, _Superclass, _EnclosingObject, _Metaclass,
              _Origin, _Factory),
    Mixin).

% @latex equation:slot-layout
% @variant missing-class
% @lean Newspeak.Program.ownSlots
% @mode own_slots(+,+,+,-)
own_slots(Program, Heap, Class, []) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, none),
    program_mixins(Program, _Mixins).

% @latex equation:slot-layout
% @variant missing-mixin
% @lean Newspeak.Program.ownSlots
% @mode own_slots(+,+,+,-)
own_slots(Program, Heap, Class, []) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_mixin(ClassDefinition, Mixin),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, none).

% @latex equation:slot-layout
% @variant found
% @lean Newspeak.Program.ownSlots
% @mode own_slots(+,+,+,-)
own_slots(Program, Heap, Class, Slots) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_mixin(ClassDefinition, Mixin),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, Mixin, some(MixinDefinition)),
    mixin_own_slots(MixinDefinition, Declarations),
    application_slots(Class, Declarations, Slots).

% @latex equation:slot-layout
% @variant qualify-empty
% @lean Newspeak.PrologBridge.PrologApplicationSlots.nil
% @mode application_slots(+,+,-)
application_slots(_Application, [], []).

% @latex equation:slot-layout
% @variant qualify-cons
% @lean Newspeak.PrologBridge.PrologApplicationSlots.cons
% @mode application_slots(+,+,-)
application_slots(Application, [Declaration|Declarations],
    [slot_address(Application, Declaration)|Slots]) :-
    application_slots(Application, Declarations, Slots).

% @latex equation:slot-layout
% @variant chain-empty
% @lean Newspeak.Program.layoutForChain
% @mode layout_for_chain(+,+,+,-)
layout_for_chain(_Program, _Heap, [], []).

% @latex equation:slot-layout
% @variant chain-cons
% @lean Newspeak.Program.layoutForChain
% @mode layout_for_chain(+,+,+,-)
layout_for_chain(Program, Heap, [Class|Ancestors], Layout) :-
    layout_for_chain(Program, Heap, Ancestors, AncestorLayout),
    own_slots(Program, Heap, Class, OwnSlots),
    list_append(AncestorLayout, OwnSlots, Layout).

% @latex equation:slot-layout
% @variant not-member-empty
% @lean Newspeak.PrologBridge.PrologListNotMember.nil
% @mode list_not_member(+,+)
list_not_member(_Value, []).

% @latex equation:slot-layout
% @variant not-member-cons
% @lean Newspeak.PrologBridge.PrologListNotMember.cons
% @mode list_not_member(+,+)
list_not_member(Value, [Head|Tail]) :-
    dif(Value, Head),
    list_not_member(Value, Tail).

% @latex equation:slot-layout
% @variant nodup-empty
% @lean List.Nodup.nil
% @mode list_nodup(+)
list_nodup([]).

% @latex equation:slot-layout
% @variant nodup-cons
% @lean List.Nodup.cons
% @mode list_nodup(+)
list_nodup([Head|Tail]) :-
    list_not_member(Head, Tail),
    list_nodup(Tail).

% @latex equation:slot-layout
% @lean Newspeak.Program.InstanceLayout
% @mode instance_layout(+,+,+,-)
instance_layout(Program, Heap, Class, Layout) :-
    class_chain(Program, Heap, Class, Chain),
    layout_for_chain(Program, Heap, Chain, Layout),
    list_nodup(Layout).

% @latex rule:Factory-New
% @variant slots-empty
% @lean Newspeak.Program.slotsInitializedTo
% @mode slots_initialized_to(+,+,-)
slots_initialized_to([], _Value, store([])).

% @latex rule:Factory-New
% @variant slots-cons
% @lean Newspeak.Program.slotsInitializedTo
% @mode slots_initialized_to(+,+,-)
slots_initialized_to([Slot|Slots], Value, store([entry(Slot, Value)|Entries])) :-
    slots_initialized_to(Slots, Value, store(Entries)).

% @latex rule:Factory-New
% @variant allocate-object
% @lean Newspeak.Program.allocateInstance
% @mode allocate_instance(+,+,+,+,+,-,-)
allocate_instance(
    _Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Class, Layout, NilObject,
    allocation_state(NewHeap, NextMirror, NextActivation, NextClosure,
                     succ(NextObject), NextClass),
    object_id(NextObject)) :-
    slots_initialized_to(Layout, NilObject, Slots),
    heap_install_object(
        Heap, object_id(NextObject),
        object_def(Class, Slots, store([]), none), NewHeap).

% @latex equation:instance-initializer-activation
% @lean Newspeak.Program.initializerActivationDefinition
% @mode initializer_activation_definition(+,+,+,+,+,+,+,-)
initializer_activation_definition(
    Program, Id, Factory, Class, Object, Message, Continuation,
    activation_def(
        ActivationClass, initializer_provenance(Declaration), Parameters,
        store([]), ordinary_object(Object), some(Class), Continuation,
        some(Id), true, store([entry(Declaration, Id)]), store([]))) :-
    activation_class(Program, ActivationClass),
    factory_activation_declaration(Factory, Declaration),
    factory_parameters(Factory, FormalParameters),
    message_arguments(Message, Arguments),
    bind_parameters(FormalParameters, Arguments, Parameters).

% @latex equation:instance-initializer-activation
% @lean Newspeak.Program.allocateInitializerActivation
% @mode allocate_initializer_activation(+,+,+,+,+,+,+,-,-)
allocate_initializer_activation(
    Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Factory, Class, Object, Message, Continuation,
    allocation_state(NewHeap, NextMirror, succ(NextActivation), NextClosure,
                     NextObject, NextClass),
    activation_id(NextActivation)) :-
    initializer_activation_definition(
        Program, activation_id(NextActivation), Factory, Class, Object,
        Message, Continuation, Activation),
    heap_install_activation(
        Heap, activation_id(NextActivation), Activation, NewHeap).

% @latex rule:Factory-New
% @variant combined-allocation
% @lean Newspeak.Program.allocateInitialInstance
% @mode allocate_initial_instance(+,+,+,+,+,+,+,-,-,-)
allocate_initial_instance(
    Program, State, Class, Layout, Factory, Message, Continuation,
    FinalState, Object, Initializer) :-
    program_nil_object(Program, NilObject),
    allocate_instance(
        Program, State, Class, Layout, NilObject, ObjectState, Object),
    allocate_initializer_activation(
        Program, ObjectState, Factory, Class, Object, Message, Continuation,
        FinalState, Initializer).

% @latex rule:Factory-New
% @variant result
% @lean Newspeak.Program.factoryNewResult
% @mode factory_new_result(+,+,+,+,+,+,+,+,+,-)
factory_new_result(
    Program, State, Rest, Current, Frames, Class, Layout, Factory, Message,
    sequential_config(
        FinalState,
        activation_stack_push(
            activation_stack_push(
                Rest,
                activation_frame(
                    Current, eval_stack_push(Frames, return_frame))),
            activation_frame(Initializer, eval_stack_empty)),
        init_class(Class, Object, Message))) :-
    allocate_initial_instance(
        Program, State, Class, Layout, Factory, Message, some(Current),
        FinalState, Object, Initializer).

% @latex rule:Factory-New
% @lean Newspeak.Program.FactoryNewStep.allocate
% @mode factory_new_step(+,+,-)
factory_new_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current, eval_stack_push(Frames, return_frame))),
        evaluate(new_instance_current(Selector, Parameters))),
    After) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, class_object(Class)),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_primary_factory(ClassDefinition, some(Factory)),
    factory_selector(Factory, Selector),
    factory_parameters(Factory, Parameters),
    activation_parameter_values(Activation, Parameters, Arguments),
    instance_layout(Program, Heap, Class, Layout),
    factory_new_result(
        Program, State, Rest, Current, Frames, Class, Layout, Factory,
        message(Selector, Arguments), After).

% --------------------------------------------------------------------------
% Superclass and applied-mixin initialization coordination
% --------------------------------------------------------------------------

% @latex equation:init-class
% @lean Newspeak.ClassDef.superclass
% @mode class_superclass(+,-)
class_superclass(
    class_def(_Mixin, Superclass, _EnclosingObject, _Metaclass,
              _Origin, _Factory),
    Superclass).

% @latex equation:init-class
% @lean Newspeak.FactoryDef.plan
% @mode factory_plan(+,-)
factory_plan(
    factory_def(_ActivationDeclaration, _Selector, _Parameters, Plan), Plan).

% @latex equation:init-class
% @variant body-plan
% @lean Newspeak.InitializerPlan.superclassMessage
% @mode initializer_plan_superclass_message(+,-)
initializer_plan_superclass_message(
    body_plan(Message), Message).

% @latex equation:init-class
% @variant applied-plan
% @lean Newspeak.InitializerPlan.superclassMessage
% @mode initializer_plan_superclass_message(+,-)
initializer_plan_superclass_message(
    applied_mixin_plan(Message, _MixinMessage), Message).

% @latex equation:mixin-initializer-activation
% @lean Newspeak.MixinDef.initializerDeclaration
% @mode mixin_initializer_declaration(+,-)
mixin_initializer_declaration(
    mixin_def(_Declaration, _Methods, _OwnSlots, _NestedDeclarations,
              InitializerDeclaration, _InitializerSelector,
              _InitializerParameters, _InitializerGroups, _InitializerBody),
    InitializerDeclaration).

% @latex equation:mixin-initializer
% @lean Newspeak.MixinDef.initializerSelector
% @mode mixin_initializer_selector(+,-)
mixin_initializer_selector(
    mixin_def(_Declaration, _Methods, _OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, InitializerSelector,
              _InitializerParameters, _InitializerGroups, _InitializerBody),
    InitializerSelector).

% @latex equation:mixin-initializer
% @lean Newspeak.MixinDef.initializerParameters
% @mode mixin_initializer_parameters(+,-)
mixin_initializer_parameters(
    mixin_def(_Declaration, _Methods, _OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, _InitializerSelector,
              InitializerParameters, _InitializerGroups, _InitializerBody),
    InitializerParameters).

% @latex equation:mixin-initializer
% @lean Newspeak.MixinDef.initializerGroups
% @mode mixin_initializer_groups(+,-)
mixin_initializer_groups(
    mixin_def(_Declaration, _Methods, _OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, _InitializerSelector,
              _InitializerParameters, InitializerGroups, _InitializerBody),
    InitializerGroups).

% @latex equation:mixin-initializer
% @lean Newspeak.MixinDef.initializerBody
% @mode mixin_initializer_body(+,-)
mixin_initializer_body(
    mixin_def(_Declaration, _Methods, _OwnSlots, _NestedDeclarations,
              _InitializerDeclaration, _InitializerSelector,
              _InitializerParameters, _InitializerGroups, InitializerBody),
    InitializerBody).

% @latex rule:Init-Super
% @variant message-matches
% @lean Newspeak.Message.matchesInitializer
% @mode message_initializer_match(+,+,+,-)
message_initializer_match(
    message(Selector, Arguments), Selector, Parameters, true) :-
    list_length(Arguments, Arity),
    list_length(Parameters, Arity).

% @latex rule:Init-Super
% @variant selector-mismatch
% @lean Newspeak.Message.matchesInitializer
% @mode message_initializer_match(+,+,+,-)
message_initializer_match(
    message(MessageSelector, _Arguments), Selector, _Parameters, false) :-
    dif(MessageSelector, Selector).

% @latex rule:Init-Super
% @variant arity-mismatch
% @lean Newspeak.Message.matchesInitializer
% @mode message_initializer_match(+,+,+,-)
message_initializer_match(
    message(Selector, Arguments), Selector, Parameters, false) :-
    list_length(Arguments, ArgumentArity),
    list_length(Parameters, ParameterArity),
    dif(ArgumentArity, ParameterArity).

% @latex equation:mixin-initializer-activation
% @lean Newspeak.Program.mixinInitializerActivationDefinition
% @mode mixin_initializer_activation_definition(+,+,+,+,+,+,+,-)
mixin_initializer_activation_definition(
    Program, Id, Mixin, Class, Object, Message, Continuation,
    activation_def(
        ActivationClass, initializer_provenance(Declaration), Parameters,
        store([]), ordinary_object(Object), some(Class), Continuation,
        some(Id), true, store([entry(Declaration, Id)]), store([]))) :-
    activation_class(Program, ActivationClass),
    mixin_initializer_declaration(Mixin, Declaration),
    mixin_initializer_parameters(Mixin, FormalParameters),
    message_arguments(Message, Arguments),
    bind_parameters(FormalParameters, Arguments, Parameters).

% @latex equation:mixin-initializer-activation
% @lean Newspeak.Program.allocateMixinInitializerActivation
% @mode allocate_mixin_initializer_activation(+,+,+,+,+,+,+,-,-)
allocate_mixin_initializer_activation(
    Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Mixin, Class, Object, Message, Continuation,
    allocation_state(NewHeap, NextMirror, succ(NextActivation), NextClosure,
                     NextObject, NextClass),
    activation_id(NextActivation)) :-
    mixin_initializer_activation_definition(
        Program, activation_id(NextActivation), Mixin, Class, Object,
        Message, Continuation, Activation),
    heap_install_activation(
        Heap, activation_id(NextActivation), Activation, NewHeap).

% @latex equation:init-class
% @lean Newspeak.Program.startSuperclassInitialization
% @mode start_superclass_initialization(+,+,+,+,+,+,+,+,+,-)
start_superclass_initialization(
    _Program, State, Rest, Current, Frames, Class, Object, Original, Factory,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    superclass_message(Class, Object, Original)))),
        evaluate_message(SuperclassMessage))) :-
    factory_plan(Factory, Plan),
    initializer_plan_superclass_message(Plan, SuperclassMessage).

% @latex rule:Init-Super
% @lean Newspeak.Program.invokeSuperclassInitializer
% @mode invoke_superclass_initializer(+,+,+,+,+,+,+,+,+,+,+,-)
invoke_superclass_initializer(
    Program, State, Rest, Current, Frames, Class, Superclass, Object,
    Original, Factory, Message,
    sequential_config(
        NewState,
        activation_stack_push(
            activation_stack_push(
                Rest,
                activation_frame(
                    Current,
                    eval_stack_push(
                        Frames,
                        after_superclass(Class, Object, Original)))),
            activation_frame(NewActivation, eval_stack_empty)),
        init_class(Superclass, Object, Message))) :-
    allocate_initializer_activation(
        Program, State, Factory, Superclass, Object, Message, some(Current),
        NewState, NewActivation).

% @latex equation:applied-own-init
% @lean Newspeak.Program.startMixinInitialization
% @mode start_mixin_initialization(+,+,+,+,+,+,+,-)
start_mixin_initialization(
    State, Rest, Current, Frames, Class, Object, Message,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, mixin_message(Class, Object)))),
        evaluate_message(Message))).

% @latex rule:Init-Applied-Mixin
% @lean Newspeak.Program.invokeMixinInitializer
% @mode invoke_mixin_initializer(+,+,+,+,+,+,+,+,+,-)
invoke_mixin_initializer(
    Program, State, Rest, Current, Frames, Class, Object, Mixin, Message,
    sequential_config(
        NewState,
        activation_stack_push(
            activation_stack_push(
                Rest,
                activation_frame(
                    Current,
                    eval_stack_push(Frames, after_mixin(Class, Object)))),
            activation_frame(NewActivation, eval_stack_empty)),
        initialize_slot_groups(Object, Groups, Body))) :-
    allocate_mixin_initializer_activation(
        Program, State, Mixin, Class, Object, Message, some(Current),
        NewState, NewActivation),
    mixin_initializer_groups(Mixin, Groups),
    mixin_initializer_body(Mixin, Body).

% @latex equation:init-class
% @variant at-top
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        init_class(Class, Object, Original)),
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        own_initialization(Class, Object, Original))) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_superclass(ClassDefinition, Superclass),
    top_class(Program, Superclass).

% @latex equation:init-class
% @variant start-superclass
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        init_class(Class, Object, Original)),
    After) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_superclass(ClassDefinition, Superclass),
    top_class(Program, Top),
    dif(Superclass, Top),
    class_primary_factory(ClassDefinition, some(Factory)),
    start_superclass_initialization(
        Program, State, Rest, Current, Frames, Class, Object, Original,
        Factory, After).

% @latex rule:Init-Super
% @variant invoke
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    superclass_message(Class, Object, Original)))),
        message_value(Message)),
    After) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_superclass(ClassDefinition, Superclass),
    store_lookup(Classes, Superclass, some(SuperclassDefinition)),
    class_primary_factory(SuperclassDefinition, some(Factory)),
    factory_selector(Factory, Selector),
    factory_parameters(Factory, Parameters),
    message_initializer_match(Message, Selector, Parameters, true),
    invoke_superclass_initializer(
        Program, State, Rest, Current, Frames, Class, Superclass, Object,
        Original, Factory, Message, After).

% @latex rule:Init-Super
% @variant wrong-factory
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    superclass_message(Class, Object, Original)))),
        message_value(Message)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(wrong_factory))) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_superclass(ClassDefinition, Superclass),
    store_lookup(Classes, Superclass, some(SuperclassDefinition)),
    class_primary_factory(SuperclassDefinition, some(Factory)),
    factory_selector(Factory, Selector),
    factory_parameters(Factory, Parameters),
    message_initializer_match(Message, Selector, Parameters, false).

% @latex rule:Init-Applied-Mixin
% @variant invoke
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, mixin_message(Class, Object)))),
        message_value(Message)),
    After) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_mixin(ClassDefinition, MixinId),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, some(Mixin)),
    mixin_initializer_selector(Mixin, Selector),
    mixin_initializer_parameters(Mixin, Parameters),
    message_initializer_match(Message, Selector, Parameters, true),
    invoke_mixin_initializer(
        Program, State, Rest, Current, Frames, Class, Object, Mixin, Message,
        After).

% @latex rule:Init-Applied-Mixin
% @variant wrong-factory
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, mixin_message(Class, Object)))),
        message_value(Message)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(wrong_factory))) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_mixin(ClassDefinition, MixinId),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, some(Mixin)),
    mixin_initializer_selector(Mixin, Selector),
    mixin_initializer_parameters(Mixin, Parameters),
    message_initializer_match(Message, Selector, Parameters, false).

% @latex equation:after-super
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, after_superclass(Class, Object, Original)))),
        object(ordinary_object(Object))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        own_initialization(Class, Object, Original))).

% @latex equation:after-mixin
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, after_mixin(_Class, Object)))),
        object(ordinary_object(Object))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        finish(ordinary_object(Object)))).

% @latex equation:body-own-init
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        own_initialization(Class, Object, _Original)),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        initialize_slot_groups(Object, Groups, Body))) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_primary_factory(ClassDefinition, some(Factory)),
    class_mixin(ClassDefinition, MixinId),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, some(Mixin)),
    factory_plan(Factory, body_plan(_SuperclassMessage)),
    mixin_initializer_groups(Mixin, Groups),
    mixin_initializer_body(Mixin, Body).

% @latex equation:applied-own-init
% @lean Newspeak.Program.initializationCoordinatorNext
% @mode initialization_coordinator_step(+,+,-)
initialization_coordinator_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        own_initialization(Class, Object, _Original)),
    After) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_primary_factory(ClassDefinition, some(Factory)),
    class_mixin(ClassDefinition, MixinId),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, MixinId, some(_Mixin)),
    factory_plan(
        Factory, applied_mixin_plan(_SuperclassMessage, MixinMessage)),
    start_mixin_initialization(
        State, Rest, Current, Frames, Class, Object, MixinMessage, After).

% The complete instance-initialization relation is the disjoint union of its
% allocation, coordinator, and physical slot-group phases.
% @latex rule:Factory-New
% @variant instance-initialization-factory
% @lean Newspeak.Program.InstanceInitializationStep.factory
% @mode instance_initialization_step(+,+,-)
instance_initialization_step(Program, Before, After) :-
    factory_new_step(Program, Before, After).

% @latex equation:init-class
% @variant instance-initialization-coordinator
% @lean Newspeak.Program.InstanceInitializationStep.coordinator
% @mode instance_initialization_step(+,+,-)
instance_initialization_step(Program, Before, After) :-
    initialization_coordinator_step(Program, Before, After).

% @latex equation:init-sequential
% @variant instance-initialization-slots
% @lean Newspeak.Program.InstanceInitializationStep.slots
% @mode instance_initialization_step(+,+,-)
instance_initialization_step(Program, Before, After) :-
    slot_initialization_step(Program, Before, After).

% --------------------------------------------------------------------------
% Class-construction support equations
% --------------------------------------------------------------------------

% @latex equation:program-definition
% @variant class-bodies
% @lean Newspeak.Program.classBodies
% @mode program_class_bodies(+,-)
program_class_bodies(Program, Bodies) :-
    program_field(Program, class_bodies, Bodies).

% @latex equation:program-definition
% @variant mixin-applications
% @lean Newspeak.Program.mixinApplications
% @mode program_mixin_applications(+,-)
program_mixin_applications(Program, Applications) :-
    program_field(Program, mixin_applications, Applications).

% @latex equation:program-definition
% @variant class-owners
% @lean Newspeak.Program.classOwner
% @mode program_class_owners(+,-)
program_class_owners(Program, Owners) :-
    program_field(Program, class_owners, Owners).

% @latex equation:program-definition
% @variant object-literal-owners
% @lean Newspeak.Program.objectLiteralOwner
% @mode program_object_literal_owners(+,-)
program_object_literal_owners(Program, Owners) :-
    program_field(Program, object_literal_owners, Owners).

% @latex equation:distinguished-platform-classes
% @variant class-class
% @lean Newspeak.Program.classClass
% @mode class_class(+,-)
class_class(Program, Class) :-
    program_field(Program, class_class, Class).

% @latex equation:distinguished-platform-classes
% @variant metaclass-class
% @lean Newspeak.Program.metaclassClass
% @mode metaclass_class(+,-)
metaclass_class(Program, Class) :-
    program_field(Program, metaclass_class, Class).

% @latex equation:factory-selector
% @variant message-template-selector
% @lean Newspeak.MessageTemplate.selector
% @mode message_template_selector(+,-)
message_template_selector(message_template(Selector, _Arguments), Selector).

% @latex equation:class-enclosing-object
% @variant activation-owner
% @lean Newspeak.Program.classEnclosingObject
% @mode class_enclosing_object(+,+,+,+,-)
class_enclosing_object(
    Program, _Heap, Activation, Declaration,
    some(activation_object(Activation))) :-
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(activation_owner)).

% @latex equation:class-enclosing-object
% @variant class-owner
% @lean Newspeak.Program.classEnclosingObject
% @mode class_enclosing_object(+,+,+,+,-)
class_enclosing_object(Program, Heap, Activation, Declaration, Result) :-
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(class_owner)),
    activation_at(Heap, Activation, ActivationResult),
    class_enclosing_object_from_activation(ActivationResult, Result).

% @latex equation:class-enclosing-object
% @variant object-literal-owner
% @lean Newspeak.Program.classEnclosingObject
% @mode class_enclosing_object(+,+,+,+,-)
class_enclosing_object(Program, Heap, Activation, Declaration, Result) :-
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(object_literal_owner)),
    activation_at(Heap, Activation, ActivationResult),
    class_enclosing_object_from_activation(ActivationResult, Result).

% @latex equation:class-enclosing-object
% @variant top-owner
% @lean Newspeak.Program.classEnclosingObject
% @mode class_enclosing_object(+,+,+,+,-)
class_enclosing_object(Program, _Heap, _Activation, Declaration, some(Nil)) :-
    program_class_owners(Program, Owners),
    store_lookup(Owners, Declaration, some(top_owner)),
    program_nil_object(Program, Nil).

% @latex equation:class-enclosing-object
% @variant missing-activation
% @lean Option.map
% @mode class_enclosing_object_from_activation(+,-)
class_enclosing_object_from_activation(none, none).

% @latex equation:class-enclosing-object
% @variant live-activation
% @lean Option.map
% @mode class_enclosing_object_from_activation(+,-)
class_enclosing_object_from_activation(some(Activation), some(Receiver)) :-
    activation_receiver(Activation, Receiver).

% @latex equation:inheritance-error
% @variant missing-class
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(Heap, class_object(Class), _Message,
                  some(class_expected)) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, none).

% @latex equation:inheritance-error
% @variant non-instantiable
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(Heap, class_object(Class), _Message,
                  some(class_not_instantiable)) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_primary_factory(ClassDefinition, none).

% @latex equation:inheritance-error
% @variant valid
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(Heap, class_object(Class), Message, none) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_primary_factory(ClassDefinition, some(Factory)),
    factory_selector(Factory, Selector),
    message_template_selector(Message, Selector).

% @latex equation:inheritance-error
% @variant wrong-factory
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(Heap, class_object(Class), Message, some(wrong_factory)) :-
    heap_classes(Heap, Classes),
    store_lookup(Classes, Class, some(ClassDefinition)),
    class_primary_factory(ClassDefinition, some(Factory)),
    factory_selector(Factory, FactorySelector),
    message_template_selector(Message, MessageSelector),
    dif(FactorySelector, MessageSelector).

% @latex equation:inheritance-error
% @variant ordinary-object
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(_Heap, ordinary_object(_Object), _Message,
                  some(class_expected)).

% @latex equation:inheritance-error
% @variant mixin-object
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(_Heap, mixin_object(_Mixin), _Message,
                  some(class_expected)).

% @latex equation:inheritance-error
% @variant activation-object
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(_Heap, activation_object(_Activation), _Message,
                  some(class_expected)).

% @latex equation:inheritance-error
% @variant closure-object
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(_Heap, closure_object(_Closure), _Message,
                  some(class_expected)).

% @latex equation:inheritance-error
% @variant mirror-object
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(_Heap, mirror_object(_Mirror), _Message,
                  some(class_expected)).

% @latex equation:inheritance-error
% @variant actor-object
% @lean Newspeak.Program.inheritanceError
% @mode inheritance_error(+,+,+,-)
inheritance_error(_Heap, actor_object(_Actor), _Message,
                  some(class_expected)).

% @latex equation:factory-descriptor
% @variant body-factory
% @lean Newspeak.Program.bodyFactory
% @mode body_factory(+,-)
body_factory(
    class_body_descriptor(
        _Declaration, _SuperclassSyntax, FactorySelector, FactoryParameters,
        _InstanceMixin, _ClassMixin, InitializerDeclaration,
        SuperclassMessage),
    factory_def(
        InitializerDeclaration, FactorySelector, FactoryParameters,
        body_plan(SuperclassMessage))).

% @latex equation:factory-descriptor
% @variant application-factory
% @lean Newspeak.Program.applicationFactory
% @mode application_factory(+,-)
application_factory(
    mixin_application_descriptor(
        _Declaration, FactorySelector, FactoryParameters, _ClassMixin,
        InitializerDeclaration, SuperclassMessage, MixinMessage),
    factory_def(
        InitializerDeclaration, FactorySelector, FactoryParameters,
        applied_mixin_plan(SuperclassMessage, MixinMessage))).

% @latex equation:body-descriptor
% @lean Newspeak.ClassBodyDescriptor
% @mode class_body_descriptor_fields(+,-,-,-,-,-,-,-,-)
class_body_descriptor_fields(
    class_body_descriptor(
        Declaration, SuperclassSyntax, FactorySelector, FactoryParameters,
        InstanceMixin, ClassMixin, InitializerDeclaration, SuperclassMessage),
    Declaration, SuperclassSyntax, FactorySelector, FactoryParameters,
    InstanceMixin, ClassMixin, InitializerDeclaration, SuperclassMessage).

% @latex equation:application-descriptor
% @lean Newspeak.MixinApplicationDescriptor
% @mode mixin_application_descriptor_fields(+,-,-,-,-,-,-,-)
mixin_application_descriptor_fields(
    mixin_application_descriptor(
        Declaration, FactorySelector, FactoryParameters, ClassMixin,
        InitializerDeclaration, SuperclassMessage, MixinMessage),
    Declaration, FactorySelector, FactoryParameters, ClassMixin,
    InitializerDeclaration, SuperclassMessage, MixinMessage).

% @latex equation:allocate-class
% @variant heap-install-class
% @lean Newspeak.Heap.installClass
% @mode heap_install_class(+,+,+,-)
heap_install_class(heap(Fields), Class, Definition, heap(NewFields)) :-
    store_lookup(Fields, classes, some(Classes)),
    store_install(Classes, Class, Definition, NewClasses),
    store_install(Fields, classes, NewClasses, NewFields).

% @latex equation:allocate-class
% @lean Newspeak.Program.allocateClassPair
% @mode allocate_class_pair(+,+,+,+,+,+,+,+,-,-,-)
allocate_class_pair(
    Program,
    allocation_state(Heap, NextMirror, NextActivation, NextClosure,
                     NextObject, NextClass),
    Origin, InstanceMixin, ClassMixin, Superclass, EnclosingObject, Factory,
    allocation_state(NewHeap, NextMirror, NextActivation, NextClosure,
                     NextObject, succ(succ(NextClass))),
    class_id(succ(NextClass)), class_id(NextClass)) :-
    class_class(Program, ClassClass),
    metaclass_class(Program, MetaclassClass),
    heap_install_class(
        Heap, class_id(NextClass),
        class_def(
            ClassMixin, ClassClass, EnclosingObject, MetaclassClass, Origin,
            none),
        MetaclassHeap),
    heap_install_class(
        MetaclassHeap, class_id(succ(NextClass)),
        class_def(
            InstanceMixin, Superclass, EnclosingObject,
            class_id(NextClass), Origin, some(Factory)),
        NewHeap).

% @latex equation:top-superclass-error
% @variant non-top
% @lean Newspeak.Program.validTopSuperclass
% @mode valid_top_superclass(+,+,+,+,-)
valid_top_superclass(Program, EnclosingObject, _Syntax, _Superclass, true) :-
    program_nil_object(Program, Nil),
    dif(EnclosingObject, Nil).

% @latex equation:top-superclass-error
% @variant implicit-object
% @lean Newspeak.Program.validTopSuperclass
% @mode valid_top_superclass(+,+,+,+,-)
valid_top_superclass(
    Program, Nil, implicit_superclass, ObjectClass, true) :-
    program_nil_object(Program, Nil),
    object_class(Program, ObjectClass).

% @latex equation:top-superclass-error
% @variant explicit
% @lean Newspeak.Program.validTopSuperclass
% @mode valid_top_superclass(+,+,+,+,-)
valid_top_superclass(Program, Nil, explicit_superclass, _Superclass, false) :-
    program_nil_object(Program, Nil).

% @latex equation:top-superclass-error
% @variant implicit-non-object
% @lean Newspeak.Program.validTopSuperclass
% @mode valid_top_superclass(+,+,+,+,-)
valid_top_superclass(
    Program, Nil, implicit_superclass, Superclass, false) :-
    program_nil_object(Program, Nil),
    object_class(Program, ObjectClass),
    dif(Superclass, ObjectClass).

% These nine clauses are the operational class-construction relation from
% Section 8.  The two commit clauses deliberately contain only the premises
% printed in the LaTeX rules.  Lean's present `ClassConstructionStep` adds a
% global post-allocation well-formedness proof to those two constructors; the
% correspondence module records that extra proof as an explicit safety
% obligation rather than silently treating it as an operational test.

% @latex rule:Class-Super
% @lean Newspeak.Program.ClassConstructionStep.bodyStart
% @mode class_construction_step(+,+,-)
class_construction_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(class_body(Declaration, SuperclassExpression))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, make_class_body(Descriptor, EnclosingObject)))),
        evaluate(SuperclassExpression))) :-
    program_class_bodies(Program, Bodies),
    store_lookup(Bodies, Declaration, some(Descriptor)),
    allocation_state_heap(State, Heap),
    class_enclosing_object(
        Program, Heap, Current, Declaration, some(EnclosingObject)).

% @latex rule:Class-Commit
% @lean Newspeak.Program.ClassConstructionStep.bodyCommit
% @mode class_construction_step(+,+,-)
class_construction_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, make_class_body(Descriptor, EnclosingObject)))),
        object(class_object(Superclass))),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(class_object(Class)))) :-
    allocation_state_heap(State, Heap),
    class_body_descriptor_fields(Descriptor,
        Declaration, SuperclassSyntax, _FactorySelector, _FactoryParameters,
        InstanceMixin, ClassMixin, _InitializerDeclaration,
        SuperclassMessage),
    inheritance_error(Heap, class_object(Superclass), SuperclassMessage, none),
    valid_top_superclass(
        Program, EnclosingObject, SuperclassSyntax, Superclass, true),
    body_factory(Descriptor, Factory),
    allocate_class_pair(
        Program, State, expression(named_class(Declaration)), InstanceMixin,
        ClassMixin, Superclass, EnclosingObject, Factory,
        NewState, Class, _Metaclass).

% @latex equation:inheritance-error-step
% @variant class-body
% @lean Newspeak.Program.ClassConstructionStep.bodyInheritanceError
% @mode class_construction_step(+,+,-)
class_construction_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, make_class_body(Descriptor, _EnclosingObject)))),
        object(Value)),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(Error))) :-
    allocation_state_heap(State, Heap),
    class_body_descriptor_fields(Descriptor,
        _Declaration, _SuperclassSyntax, _FactorySelector, _FactoryParameters,
        _InstanceMixin, _ClassMixin, _InitializerDeclaration,
        SuperclassMessage),
    inheritance_error(Heap, Value, SuperclassMessage, some(Error)).

% @latex equation:top-superclass-error
% @lean Newspeak.Program.ClassConstructionStep.bodyTopError
% @mode class_construction_step(+,+,-)
class_construction_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, make_class_body(Descriptor, Nil)))),
        object(class_object(Superclass))),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(top_superclass))) :-
    allocation_state_heap(State, Heap),
    program_nil_object(Program, Nil),
    class_body_descriptor_fields(Descriptor,
        _Declaration, SuperclassSyntax, _FactorySelector, _FactoryParameters,
        _InstanceMixin, _ClassMixin, _InitializerDeclaration,
        SuperclassMessage),
    inheritance_error(Heap, class_object(Superclass), SuperclassMessage, none),
    valid_top_superclass(
        Program, Nil, SuperclassSyntax, Superclass, false).

% @latex equation:mixin-start
% @lean Newspeak.Program.ClassConstructionStep.mixinStart
% @mode class_construction_step(+,+,-)
class_construction_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(mixin_apply(
            Declaration, SuperclassExpression, MixinExpression))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, mixin_superclass(Descriptor, MixinExpression)))),
        evaluate(SuperclassExpression))) :-
    program_mixin_applications(Program, Applications),
    store_lookup(Applications, Declaration, some(Descriptor)).

% @latex equation:mixin-right
% @lean Newspeak.Program.ClassConstructionStep.mixinSuperclassDone
% @mode class_construction_step(+,+,-)
class_construction_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    mixin_superclass(Descriptor, MixinExpression)))),
        object(class_object(Superclass))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, mixin_source(Descriptor, Superclass)))),
        evaluate(MixinExpression))) :-
    allocation_state_heap(State, Heap),
    mixin_application_descriptor_fields(Descriptor,
        _Declaration, _FactorySelector, _FactoryParameters, _ClassMixin,
        _InitializerDeclaration, SuperclassMessage, _MixinMessage),
    inheritance_error(Heap, class_object(Superclass), SuperclassMessage, none).

% @latex rule:Mixin-Commit
% @lean Newspeak.Program.ClassConstructionStep.mixinCommit
% @mode class_construction_step(+,+,-)
class_construction_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, mixin_source(Descriptor, Superclass)))),
        object(class_object(Source))),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(class_object(Class)))) :-
    allocation_state_heap(State, Heap),
    heap_classes(Heap, Classes),
    store_lookup(Classes, Source, some(SourceDefinition)),
    class_primary_factory(SourceDefinition, some(SourceFactory)),
    mixin_application_descriptor_fields(Descriptor,
        Declaration, FactorySelector, _FactoryParameters, ClassMixin,
        _InitializerDeclaration, _SuperclassMessage, MixinMessage),
    factory_selector(SourceFactory, MixinSelector),
    message_template_selector(MixinMessage, MixinSelector),
    factory_selector(SourceFactory, FactorySelector),
    class_mixin(SourceDefinition, SourceMixin),
    class_definition_enclosing_object(
        SourceDefinition, SourceEnclosingObject),
    application_factory(Descriptor, Factory),
    allocate_class_pair(
        Program, State, expression(named_class(Declaration)), SourceMixin,
        ClassMixin, Superclass, SourceEnclosingObject, Factory,
        NewState, Class, _Metaclass).

% @latex equation:inheritance-error-step
% @variant mixin-superclass
% @lean Newspeak.Program.ClassConstructionStep.mixinSuperclassError
% @mode class_construction_step(+,+,-)
class_construction_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    mixin_superclass(Descriptor, _MixinExpression)))),
        object(Value)),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(Error))) :-
    allocation_state_heap(State, Heap),
    mixin_application_descriptor_fields(Descriptor,
        _Declaration, _FactorySelector, _FactoryParameters, _ClassMixin,
        _InitializerDeclaration, SuperclassMessage, _MixinMessage),
    inheritance_error(Heap, Value, SuperclassMessage, some(Error)).

% @latex equation:inheritance-error-step
% @variant mixin-source
% @lean Newspeak.Program.ClassConstructionStep.mixinSourceError
% @mode class_construction_step(+,+,-)
class_construction_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, mixin_source(Descriptor, _Superclass)))),
        object(Value)),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(Error))) :-
    allocation_state_heap(State, Heap),
    mixin_application_descriptor_fields(Descriptor,
        _Declaration, _FactorySelector, _FactoryParameters, _ClassMixin,
        _InitializerDeclaration, _SuperclassMessage, MixinMessage),
    inheritance_error(Heap, Value, MixinMessage, some(Error)).

% --------------------------------------------------------------------------
% Object literals and receiver-local nested classes
% --------------------------------------------------------------------------

% @latex equation:program-definition
% @variant object-literals
% @lean Newspeak.Program.objectLiterals
% @mode program_object_literals(+,-)
program_object_literals(Program, Literals) :-
    program_field(Program, object_literals, Literals).

% @latex equation:object-literal-descriptor
% @lean Newspeak.ObjectLiteralDescriptor
% @mode object_literal_descriptor_fields(+,-,-,-,-,-,-)
object_literal_descriptor_fields(
    object_literal_descriptor(
        Declaration, SuperclassSyntax, InstanceMixin, ClassMixin,
        InitializerDeclaration, SuperclassMessage),
    Declaration, SuperclassSyntax, InstanceMixin, ClassMixin,
    InitializerDeclaration, SuperclassMessage).

% @latex equation:object-literal-enclosing-object
% @variant top
% @lean Newspeak.Program.objectLiteralEnclosingObject
% @mode object_literal_enclosing_object(+,+,+,-)
object_literal_enclosing_object(Program, Heap, Activation, some(Nil)) :-
    activation_at(Heap, Activation, some(Definition)),
    activation_provenance(Definition, top_provenance),
    program_nil_object(Program, Nil).

% @latex equation:object-literal-enclosing-object
% @variant non-top
% @lean Newspeak.Program.objectLiteralEnclosingObject
% @mode object_literal_enclosing_object(+,+,+,-)
object_literal_enclosing_object(
    _Program, Heap, Activation, some(activation_object(Activation))) :-
    activation_at(Heap, Activation, some(Definition)),
    activation_provenance(Definition, Provenance),
    dif(Provenance, top_provenance).

% @latex equation:object-literal-enclosing-object
% @variant missing
% @lean Newspeak.Program.objectLiteralEnclosingObject
% @mode object_literal_enclosing_object(+,+,+,-)
object_literal_enclosing_object(_Program, Heap, Activation, none) :-
    activation_at(Heap, Activation, none).

% @latex rule:Object-Commit
% @variant factory
% @lean Newspeak.Program.objectLiteralFactory
% @mode object_literal_factory(+,+,-)
object_literal_factory(
    Descriptor, Mixin,
    factory_def(
        InitializerDeclaration, Selector, [],
        body_initializer_plan(SuperclassMessage))) :-
    object_literal_descriptor_fields(
        Descriptor, _Declaration, _SuperclassSyntax, _InstanceMixin,
        _ClassMixin, InitializerDeclaration, SuperclassMessage),
    mixin_initializer_selector(Mixin, Selector).

% @latex rule:Object-Commit
% @variant new-message
% @lean Newspeak.Program.objectLiteralNewMessage
% @mode object_literal_new_message(+,-)
object_literal_new_message(Mixin, message(Selector, [])) :-
    mixin_initializer_selector(Mixin, Selector).

% @latex equation:nested-class-cache
% @variant nested-class-store
% @lean Newspeak.ObjectDef.nestedClasses
% @mode object_nested_classes(+,-)
object_nested_classes(
    object_def(_Class, _Slots, NestedClasses, _WeakContainer), NestedClasses).

% @latex equation:nested-class-cache
% @variant missing-object
% @lean Newspeak.Heap.readNestedClass
% @mode read_nested_class(+,+,+,-)
read_nested_class(Heap, Object, _Declaration, none) :-
    object_at(Heap, Object, none).

% @latex equation:nested-class-cache
% @variant live-object
% @lean Newspeak.Heap.readNestedClass
% @mode read_nested_class(+,+,+,-)
read_nested_class(Heap, Object, Declaration, Result) :-
    object_at(Heap, Object, some(Definition)),
    object_nested_classes(Definition, NestedClasses),
    store_lookup(NestedClasses, Declaration, Result).

% @latex equation:nested-class-cache
% @variant object-update
% @lean Newspeak.Heap.writeNestedClass
% @mode object_with_nested_class(+,+,+,-)
object_with_nested_class(
    object_def(Class, Slots, NestedClasses, WeakContainer),
    Declaration, NestedClass,
    object_def(Class, Slots, NewNestedClasses, WeakContainer)) :-
    store_install(
        NestedClasses, Declaration, NestedClass, NewNestedClasses).

% @latex equation:nested-class-cache
% @variant heap-update
% @lean Newspeak.Heap.writeNestedClass
% @mode write_nested_class_heap(+,+,+,+,-)
write_nested_class_heap(Heap, Object, Declaration, NestedClass, NewHeap) :-
    object_at(Heap, Object, some(Definition)),
    object_with_nested_class(
        Definition, Declaration, NestedClass, NewDefinition),
    heap_install_object(Heap, Object, NewDefinition, NewHeap).

% @latex equation:class-with-enclosing-object
% @variant class-body
% @lean Newspeak.Program.evaluateNestedClassMiss
% @mode evaluate_nested_class_miss(+,+,+,+,+,+,+,+,-)
evaluate_nested_class_miss(
    Program, State, Rest, Current, Frames, Object, Declaration,
    class_body(ClassDeclaration, SuperclassExpression),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    eval_stack_push(
                        Frames, nested_class_store(Object, Declaration)),
                    make_class_body(
                        Descriptor, ordinary_object(Object))))),
        evaluate(SuperclassExpression))) :-
    program_class_bodies(Program, Bodies),
    store_lookup(Bodies, ClassDeclaration, some(Descriptor)).

% @latex equation:class-with-enclosing-object
% @variant mixin-application
% @lean Newspeak.Program.evaluateNestedClassMiss
% @mode evaluate_nested_class_miss(+,+,+,+,+,+,+,+,-)
evaluate_nested_class_miss(
    _Program, State, Rest, Current, Frames, Object, Declaration,
    mixin_apply(ClassDeclaration, SuperclassExpression, MixinExpression),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, nested_class_store(Object, Declaration)))),
        evaluate(
            mixin_apply(
                ClassDeclaration, SuperclassExpression, MixinExpression)))).

% @latex rule:Object-Super
% @lean Newspeak.Program.ObjectLiteralStep.superclass
% @mode object_literal_step(+,+,-)
object_literal_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(object_literal(Declaration, SuperclassExpression))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    make_object_literal(Descriptor, EnclosingObject)))),
        evaluate(SuperclassExpression))) :-
    program_object_literals(Program, Literals),
    store_lookup(Literals, Declaration, some(Descriptor)),
    allocation_state_heap(State, Heap),
    object_literal_enclosing_object(
        Program, Heap, Current, some(EnclosingObject)).

% @latex rule:Object-Commit
% @lean Newspeak.Program.ObjectLiteralStep.commit
% @mode object_literal_step(+,+,-)
object_literal_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    make_object_literal(Descriptor, EnclosingObject)))),
        object(class_object(Superclass))),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(
            ordinary_request(class_object(Class)), NewMessage))) :-
    allocation_state_heap(State, Heap),
    object_literal_descriptor_fields(
        Descriptor, Declaration, SuperclassSyntax, InstanceMixin, ClassMixin,
        InitializerDeclaration, SuperclassMessage),
    inheritance_error(
        Heap, class_object(Superclass), SuperclassMessage, none),
    valid_top_superclass(
        Program, EnclosingObject, SuperclassSyntax, Superclass, true),
    program_mixins(Program, Mixins),
    store_lookup(Mixins, InstanceMixin, some(Mixin)),
    mixin_initializer_declaration(Mixin, InitializerDeclaration),
    mixin_initializer_parameters(Mixin, []),
    object_literal_factory(Descriptor, Mixin, Factory),
    object_literal_new_message(Mixin, NewMessage),
    allocate_class_pair(
        Program, State, expression(object_literal(Declaration)),
        InstanceMixin, ClassMixin, Superclass, EnclosingObject, Factory,
        NewState, Class, _Metaclass).

% @latex equation:object-inheritance-error
% @lean Newspeak.Program.ObjectLiteralStep.inheritanceError
% @mode object_literal_step(+,+,-)
object_literal_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames,
                    make_object_literal(Descriptor, _EnclosingObject)))),
        object(Value)),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(Error))) :-
    allocation_state_heap(State, Heap),
    object_literal_descriptor_fields(
        Descriptor, _Declaration, _SuperclassSyntax, _InstanceMixin,
        _ClassMixin, _InitializerDeclaration, SuperclassMessage),
    inheritance_error(Heap, Value, SuperclassMessage, some(Error)).

% @latex equation:object-top-superclass-error
% @lean Newspeak.Program.ObjectLiteralStep.topSuperclassError
% @mode object_literal_step(+,+,-)
object_literal_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, make_object_literal(Descriptor, Nil)))),
        object(class_object(Superclass))),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(top_superclass))) :-
    allocation_state_heap(State, Heap),
    program_nil_object(Program, Nil),
    object_literal_descriptor_fields(
        Descriptor, _Declaration, SuperclassSyntax, _InstanceMixin,
        _ClassMixin, _InitializerDeclaration, SuperclassMessage),
    inheritance_error(
        Heap, class_object(Superclass), SuperclassMessage, none),
    valid_top_superclass(
        Program, Nil, SuperclassSyntax, Superclass, false).

% @latex equation:nested-class-cache
% @variant hit
% @lean Newspeak.Program.NestedClassStep.hit
% @mode nested_class_step(+,+,-)
nested_class_step(
    _Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(nested_class(Declaration, ClassExpression))),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(class_object(Class)))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, ordinary_object(Object)),
    activation_current_class(Activation, some(Application)),
    read_nested_class(Heap, Object, nested_cache(Application, Declaration), some(Class)).

% @latex equation:nested-class-cache
% @variant miss
% @lean Newspeak.Program.NestedClassStep.miss
% @mode nested_class_step(+,+,-)
nested_class_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(nested_class(Declaration, ClassExpression))),
    After) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, ordinary_object(Object)),
    activation_current_class(Activation, some(Application)),
    read_nested_class(Heap, Object, nested_cache(Application, Declaration), none),
    evaluate_nested_class_miss(
        Program, State, Rest, Current, Frames, Object, nested_cache(Application, Declaration),
        ClassExpression, After).

% @latex equation:nested-class-cache
% @variant store
% @lean Newspeak.Program.NestedClassStep.store
% @mode nested_class_step(+,+,-)
nested_class_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(
                    Frames, nested_class_store(Object, Declaration)))),
        object(class_object(Class))),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(class_object(Class)))) :-
    write_nested_class_heap(
        Heap, Object, Declaration, Class, NewHeap).

% @latex equation:nested-class-cache
% @variant object-literal-union
% @lean Newspeak.Program.ObjectAndNestedClassStep.objectLiteral
% @mode object_and_nested_class_step(+,+,-)
object_and_nested_class_step(Program, Before, After) :-
    object_literal_step(Program, Before, After).

% @latex equation:nested-class-cache
% @variant nested-class-union
% @lean Newspeak.Program.ObjectAndNestedClassStep.nestedClass
% @mode object_and_nested_class_step(+,+,-)
object_and_nested_class_step(Program, Before, After) :-
    nested_class_step(Program, Before, After).

% The sequential relations are explicit Horn unions.  Keeping these clauses
% visible closes a common audit gap: a relation may have correct leaves while
% accidentally omitting one of them from the machine's actual step relation.

% @latex equation:configuration
% @variant sequential-expression
% @lean Newspeak.Program.SequentialStep.expression
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    expression_order_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-request
% @lean Newspeak.Program.SequentialStep.request
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    request_completion_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-invocation
% @lean Newspeak.Program.SequentialStep.invocation
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    method_invocation_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-body
% @lean Newspeak.Program.SequentialStep.body
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    body_machine_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-return
% @lean Newspeak.Program.SequentialStep.returns
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    return_machine_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-closure
% @lean Newspeak.Program.SequentialStep.closure
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    closure_machine_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-object-slots
% @lean Newspeak.Program.SequentialStep.objectSlots
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    object_slot_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-classes
% @lean Newspeak.Program.SequentialStep.classes
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    class_construction_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-messages
% @lean Newspeak.Program.SequentialStep.messages
% @mode sequential_step(+,+,-)
sequential_step(Program, Before, After) :-
    message_evaluation_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-through-initialization-prior
% @lean Newspeak.Program.SequentialStepWithInitialization.prior
% @mode sequential_step_with_initialization(+,+,-)
sequential_step_with_initialization(Program, Before, After) :-
    sequential_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-through-initialization-new
% @lean Newspeak.Program.SequentialStepWithInitialization.initialization
% @mode sequential_step_with_initialization(+,+,-)
sequential_step_with_initialization(Program, Before, After) :-
    instance_initialization_step(Program, Before, After).

% @latex equation:configuration
% @variant sequential-through-objects-prior
% @lean Newspeak.Program.SequentialStepWithObjects.prior
% @mode sequential_step_with_objects(+,+,-)
sequential_step_with_objects(Program, Before, After) :-
    sequential_step_with_initialization(Program, Before, After).

% @latex equation:configuration
% @variant sequential-through-objects-new
% @lean Newspeak.Program.SequentialStepWithObjects.objects
% @mode sequential_step_with_objects(+,+,-)
sequential_step_with_objects(Program, Before, After) :-
    object_and_nested_class_step(Program, Before, After).

% --------------------------------------------------------------------------
% Exception-library boundary
% --------------------------------------------------------------------------

% `error_reification/5` is a proof-carrying graph application of the abstract
% total platform operation in Equation (8.39).  A concrete platform supplies
% these application witnesses; the Horn layer does not invent an allocator.
% @latex equation:exception-reification
% @variant application-witness
% @lean Newspeak.ErrorReifier.reify
% @mode error_reification(+,+,+,-,-)
error_reification(
    error_reification(State, Error, NewState, Exception),
    State, Error, NewState, Exception).

% @latex rule:Runtime-Error-Signal
% @lean Newspeak.Program.ExceptionBoundaryStep.runtimeError
% @mode exception_boundary_step(+,+,-)
exception_boundary_step(
    Reification,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        runtime_error(Error)),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(
            ordinary_request(Exception),
            message(selector(signal), [])))) :-
    error_reification(
        Reification, State, Error, NewState, Exception).

% @latex rule:Throw-Signal
% @lean Newspeak.Program.ExceptionBoundaryStep.thrown
% @mode exception_boundary_step(+,+,-)
exception_boundary_step(
    Reification,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        throw(Error)),
    sequential_config(
        NewState,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        dispatch(
            ordinary_request(Exception),
            message(selector(signal), [])))) :-
    error_reification(
        Reification, State, Error, NewState, Exception).

% @latex equation:configuration
% @variant sequential-through-exceptions-prior
% @lean Newspeak.Program.SequentialStepWithExceptions.prior
% @mode sequential_step_with_exceptions(+,+,+,-)
sequential_step_with_exceptions(Program, _Reification, Before, After) :-
    sequential_step_with_objects(Program, Before, After).

% @latex equation:configuration
% @variant sequential-through-exceptions-new
% @lean Newspeak.Program.SequentialStepWithExceptions.exception
% @mode sequential_step_with_exceptions(+,+,+,-)
sequential_step_with_exceptions(_Program, Reification, Before, After) :-
    exception_boundary_step(Reification, Before, After).

% --------------------------------------------------------------------------
% Compound literals and top-level termination
% --------------------------------------------------------------------------

% @latex equation:tuple-platform-bindings
% @lean Newspeak.Program.platform
% @mode program_platform_object(+,+,-)
program_platform_object(Program, Name, Object) :-
    program_field(Program, platform, Platform),
    store_lookup(Platform, Name, some(Object)).

% @latex equation:tuple-expansion
% @lean Newspeak.naturalAtom
% @mode natural_atom(+,-)
natural_atom(Value, atom(integer(Value))).

% @latex equation:tuple-expansion
% @variant final-yourself
% @lean Newspeak.tuplePutClauses
% @mode tuple_put_clauses(+,+,-)
tuple_put_clauses(_Index, [], [pair(selector(yourself), [])]).

% @latex equation:tuple-expansion
% @variant at-put
% @lean Newspeak.tuplePutClauses
% @mode tuple_put_clauses(+,+,-)
tuple_put_clauses(
    Index, [Expression|Remaining],
    [pair(
        selector('at:put:'),
        [atom(integer(Index)), Expression])|Clauses]) :-
    tuple_put_clauses(succ(Index), Remaining, Clauses).

% @latex equation:tuple-expansion
% @variant empty
% @lean Newspeak.Program.tupleExpansion
% @mode tuple_expansion(+,+,+,+,-)
tuple_expansion(
    Program, _Site, _Descriptor, [],
    some(ordinary_send(
        value(ReadOnlyTuple), selector('new:'), [atom(integer(zero))]))) :-
    program_platform_object(Program, read_only_tuple, ReadOnlyTuple).

% @latex equation:tuple-expansion
% @variant nonempty
% @lean Newspeak.Program.tupleExpansion
% @mode tuple_expansion(+,+,+,+,-)
tuple_expansion(
    Program, _Site, Descriptor, [First|Remaining],
    some(ordinary_send(
        value(ReadOnlyTuple), selector('fromArray:'),
        [cascade(
            Descriptor,
            ordinary_send(
                value(Array), selector('new:'),
                [atom(integer(Length))]),
            Clauses)]))) :-
    program_platform_object(Program, read_only_tuple, ReadOnlyTuple),
    program_platform_object(Program, array, Array),
    list_length([First|Remaining], Length),
    tuple_put_clauses(succ(zero), [First|Remaining], Clauses).

% @latex equation:cascade-expansion
% @lean Newspeak.Program.cascadeExpansion
% @mode cascade_expansion(+,+,+,-)
cascade_expansion(
    Descriptor, Receiver, Clauses,
    ordinary_send(
        cascade_closure(Descriptor, Clauses), value_selector(succ(zero)),
        [Receiver])).

% @latex equation:pattern-binding
% @lean Newspeak.patternBindingSelector
% @mode pattern_binding_expression(+,+,-)
pattern_binding_expression(
    Annotation, Immediate,
    implicit_send(selector('Pattern'), [], Annotation, Immediate)).

% @latex equation:variable-pattern-parameter
% @lean Newspeak.Program.patternVariable
% @mode program_pattern_variable(+,+,-)
program_pattern_variable(Program, Site, Result) :-
    program_field(Program, pattern_variable, Variables),
    store_lookup(Variables, Site, Result).

% @latex equation:keyword-pattern-expansion
% @variant keyword-atoms-empty
% @lean List.map
% @mode pattern_keyword_atoms(+,-)
pattern_keyword_atoms([], []).

% @latex equation:keyword-pattern-expansion
% @variant selector-spelling
% @lean Newspeak.Selector.spelling
% @mode selector_spelling(+,-)
selector_spelling(selector(Spelling), Spelling).

% @latex equation:keyword-pattern-expansion
% @variant keyword-atoms-cons
% @lean List.map
% @mode pattern_keyword_atoms(+,-)
pattern_keyword_atoms(
    [pair(Selector, _Pattern)|Remaining],
    [atom(symbol(Spelling))|Atoms]) :-
    selector_spelling(Selector, Spelling),
    pattern_keyword_atoms(Remaining, Atoms).

% @latex equation:pattern-components
% @variant wildcard
% @lean Newspeak.Program.patternExpansion
% @mode pattern_expansion(+,+,+,+,-)
pattern_expansion(
    _Program, Annotation, Immediate, wildcard_pattern,
    some(ordinary_send(
        implicit_send(selector('Pattern'), [], Annotation, Immediate),
        selector(wildcard), []))).

% @latex equation:pattern-components
% @variant literal
% @lean Newspeak.Program.patternExpansion
% @mode pattern_expansion(+,+,+,+,-)
pattern_expansion(
    _Program, Annotation, Immediate, literal_pattern(Expression),
    some(ordinary_send(
        implicit_send(selector('Pattern'), [], Annotation, Immediate),
        selector('literal:'), [Expression]))).

% @latex equation:variable-pattern-parameter
% @lean Newspeak.Program.patternExpansion
% @mode pattern_expansion(+,+,+,+,-)
pattern_expansion(
    Program, _Annotation, _Immediate, variable_pattern(Site), Result) :-
    program_pattern_variable(Program, Site, Result).

% @latex equation:pattern-components
% @variant nested
% @lean Newspeak.Program.patternExpansion
% @mode pattern_expansion(+,+,+,+,-)
pattern_expansion(
    _Program, Annotation, Immediate, nested_pattern(Pattern),
    some(pattern(Pattern, Annotation, Immediate))).

% @latex equation:pattern-components
% @variant component-empty
% @lean Newspeak.Program.patternComponentExpansions
% @mode pattern_component_expansions(+,+,+,+,-)
pattern_component_expansions(_Program, _Annotation, _Immediate, [], some([])).

% @latex equation:pattern-components
% @variant component-cons
% @lean Newspeak.Program.patternComponentExpansions
% @mode pattern_component_expansions(+,+,+,+,-)
pattern_component_expansions(
    Program, Annotation, Immediate,
    [pair(_Selector, Pattern)|Remaining], some([First|Rest])) :-
    pattern_expansion(
        Program, Annotation, Immediate, Pattern, some(First)),
    pattern_component_expansions(
        Program, Annotation, Immediate, Remaining, some(Rest)).

% @latex equation:keyword-pattern-expansion
% @lean Newspeak.Program.patternExpansion
% @mode pattern_expansion(+,+,+,+,-)
pattern_expansion(
    Program, Annotation, Immediate,
    keyword_pattern(
        KeywordTupleSite, KeywordTupleCascade,
        ComponentTupleSite, ComponentTupleCascade, Pairs),
    some(ordinary_send(
        implicit_send(selector('Pattern'), [], Annotation, Immediate),
        selector('keywords:patterns:'),
        [tuple(KeywordTupleSite, KeywordTupleCascade, Keywords),
         tuple(ComponentTupleSite, ComponentTupleCascade, Components)]))) :-
    pattern_component_expansions(
        Program, Annotation, Immediate, Pairs, some(Components)),
    pattern_keyword_atoms(Pairs, Keywords).

% @latex equation:tuple-step
% @lean Newspeak.Program.CompoundLiteralStep.tuple
% @mode compound_literal_step(+,+,-)
compound_literal_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(tuple(Site, Descriptor, Elements))),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(Expansion))) :-
    tuple_expansion(
        Program, Site, Descriptor, Elements, some(Expansion)).

% @latex equation:cascade-expansion
% @lean Newspeak.Program.CompoundLiteralStep.cascade
% @mode compound_literal_step(+,+,-)
compound_literal_step(
    _Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(cascade(Descriptor, Receiver, Clauses))),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(Expansion))) :-
    cascade_expansion(Descriptor, Receiver, Clauses, Expansion).

% @latex equation:pattern-step
% @lean Newspeak.Program.CompoundLiteralStep.pattern
% @mode compound_literal_step(+,+,-)
compound_literal_step(
    Program,
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(pattern(Value, Annotation, Immediate))),
    sequential_config(
        State, activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(Expansion))) :-
    pattern_expansion(
        Program, Annotation, Immediate, Value, some(Expansion)).

% @latex equation:configuration
% @variant sequential-through-literals-prior
% @lean Newspeak.Program.SequentialStepWithLiterals.prior
% @mode sequential_step_with_literals(+,+,+,-)
sequential_step_with_literals(Program, Reification, Before, After) :-
    sequential_step_with_exceptions(
        Program, Reification, Before, After).

% @latex equation:configuration
% @variant sequential-through-literals-new
% @lean Newspeak.Program.SequentialStepWithLiterals.compoundLiteral
% @mode sequential_step_with_literals(+,+,+,-)
sequential_step_with_literals(Program, _Reification, Before, After) :-
    compound_literal_step(Program, Before, After).

% @latex rule:Top-Halt
% @variant stopped-activation
% @lean Newspeak.Program.stopTopLevelActivation
% @mode stop_top_level_activation(+,+,+,-)
stop_top_level_activation(
    allocation_state(
        Heap, NextMirror, NextActivation, NextClosure, NextObject, NextClass),
    Activation, Definition,
    allocation_state(
        NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
        NextClass)) :-
    mark_activation_uncontinuable(Definition, Stopped),
    heap_install_activation(Heap, Activation, Stopped, NewHeap).

% @latex rule:Top-Halt
% @lean Newspeak.Program.TopLevelHaltStep.halt
% @mode top_level_halt_step(+,+,-)
top_level_halt_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(
            activation_stack_empty,
            activation_frame(Current, eval_stack_empty)),
        object(Value)),
    sequential_config(NewState, activation_stack_empty, halt_control(Value))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_provenance(Activation, top_provenance),
    stop_top_level_activation(
        State, Current, Activation, NewState).

% @latex equation:configuration
% @variant sequential-through-top-prior
% @lean Newspeak.Program.SequentialStepWithTopLevel.prior
% @mode sequential_step_with_top_level(+,+,+,-)
sequential_step_with_top_level(Program, Reification, Before, After) :-
    sequential_step_with_literals(Program, Reification, Before, After).

% @latex equation:configuration
% @variant sequential-through-top-halt
% @lean Newspeak.Program.SequentialStepWithTopLevel.topHalt
% @mode sequential_step_with_top_level(+,+,+,-)
sequential_step_with_top_level(Program, _Reification, Before, After) :-
    top_level_halt_step(Program, Before, After).

% @latex equation:current-slot-operations
% @variant read
% @lean Newspeak.Program.ObjectSlotStep.currentRead
% @mode object_slot_step(+,+,-)
object_slot_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(current_read(Slot))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(read_slot(Object, slot_address(Application, Slot))))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, ordinary_object(Object)),
    activation_current_class(Activation, some(Application)).

% @latex equation:current-slot-operations
% @variant write
% @lean Newspeak.Program.ObjectSlotStep.currentWrite
% @mode object_slot_step(+,+,-)
object_slot_step(
    _Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(current_write(Slot, Expression))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(write_slot(Object, slot_address(Application, Slot), Expression)))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, ordinary_object(Object)),
    activation_current_class(Activation, some(Application)).

% @latex equation:lazy-read
% @variant hit
% @lean Newspeak.Program.ObjectSlotStep.lazyHit
% @mode object_slot_step(+,+,-)
object_slot_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(lazy_read(Slot, Initializer))),
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Value))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, ordinary_object(Object)),
    activation_current_class(Activation, some(Application)),
    read_object_slot_value(Heap, Object, slot_address(Application, Slot), Value),
    program_nil_object(Program, Nil),
    dif(Value, Nil).

% @latex equation:lazy-read
% @variant miss
% @lean Newspeak.Program.ObjectSlotStep.lazyMiss
% @mode object_slot_step(+,+,-)
object_slot_step(
    Program,
    sequential_config(
        State,
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        evaluate(lazy_read(Slot, Initializer))),
    sequential_config(
        State,
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, lazy_slot_store(Object, slot_address(Application, Slot))))),
        evaluate(Initializer))) :-
    allocation_state_heap(State, Heap),
    activation_at(Heap, Current, some(Activation)),
    activation_receiver(Activation, ordinary_object(Object)),
    activation_current_class(Activation, some(Application)),
    program_nil_object(Program, Nil),
    read_object_slot_value(Heap, Object, slot_address(Application, Slot), Nil).

% @latex equation:lazy-read
% @variant commit
% @lean Newspeak.Program.ObjectSlotStep.lazyCommit
% @mode object_slot_step(+,+,-)
object_slot_step(
    _Program,
    sequential_config(
        allocation_state(
            Heap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(
            Rest,
            activation_frame(
                Current,
                eval_stack_push(Frames, lazy_slot_store(Object, Slot)))),
        object(Value)),
    sequential_config(
        allocation_state(
            NewHeap, NextMirror, NextActivation, NextClosure, NextObject,
            NextClass),
        activation_stack_push(Rest, activation_frame(Current, Frames)),
        object(Value))) :-
    write_object_slot_heap(Heap, Object, Slot, Value, NewHeap).
