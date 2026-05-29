# Aliens and the JS bridge in primordialsoup

Date: 2026-05-28
Purpose: ground truth for what works, what doesn't, and what goes wrong at the
Newspeak ↔ JavaScript boundary on primordialsoup. Supersedes and absorbs
`NEWSPEAK_JS_PROMISE_NOTES_2026-05-18.md` (kept as a focused historical record
of the original then-pathology incident).

The empirical events behind this doc:
- 2026-05-18 — `document.documentElement` arrived where a Gemini JSON response
  belonged; root cause: raising inside a JS-Promise `then:` closure corrupts
  the alien stack.
- 2026-05-28 — `rawPush:` does-not-understand `index` on a Newspeak `List`
  returned from a `then:` closure; root cause: only a fixed set of Newspeak
  values round-trips through the alien bridge, and `List` is not one of them.

These are both symptoms of how the bridge actually works. Once you know the
mechanism, both are predictable.

## 1. Architecture

### The alien table

On the JS side, primordialsoup keeps a single growing array
`Module.aliens[]`. The first five slots are seeded once at startup
(`vm/main_emscripten.cc`):

| index | value       |
|-------|-------------|
|   0   | `undefined` |
|   1   | `null`      |
|   2   | `false`     |
|   3   | `true`      |
|   4   | `window`    |

Everything else is dynamically pushed and popped. The array doubles as the
**parameter-passing stack** between Newspeak and JS — there is no separate
calling convention. Both sides agree to `push` / `peek` / `pop` in matching
order around each cross-language call.

### The Newspeak `Alien` class

`primordialsoup/newspeak/JSForPrimordialSoup.ns` defines `Alien` with one
piece of instance state:

```newspeak
class Alien withIndex: i = (|
    public index <Integer> = i.
|)
```

That `index` is the only thing that distinguishes one alien from another to
the Newspeak side — everything else lives in JS. An `Alien` is *just* a
typed integer that names a slot in `Module.aliens[]`. Every operation the
Newspeak code does on an alien immediately punches across to JS:

```newspeak
public at: key = (
    rawPushAlien: self index.   "push receiver"
    rawPush: key.               "push key"
    rawPerformGet.              "JS Reflect.get(receiver, key); result on stack"
    ^rawPop                     "pop into Newspeak"
)
```

### The 13 JS primitives

`primordialsoup/vm/primitives.cc` defines exactly thirteen JS primitives,
numbered 154–167. Every alien operation in Newspeak is built out of these:

| #   | Newspeak method               | What it does on the JS side                                |
|-----|-------------------------------|------------------------------------------------------------|
| 154 | `rawPush:`                    | `aliens.push(<Newspeak value or alien>)`                   |
| 155 | `rawPushAlien:`               | `aliens.push(aliens[index])`                               |
| 156 | `rawPushExpat:`               | `aliens.push(<a JS function that calls back into Newspeak>)` |
| 157 | `rawPop`                      | top → Newspeak; wraps as `Alien withIndex: top`            |
| 158 | `rawPopAgain` / `alienTableSize` | top → Newspeak as a small integer (the raw index)       |
| 160 | `rawPerformGet`               | `Reflect.get(receiver, selector)`                          |
| 161 | `rawPerformSet`               | `Reflect.set(receiver, selector, value)`                   |
| 162 | `rawPerformDelete`            | `Reflect.deleteProperty(receiver, selector)`               |
| 163 | `rawPerformCall:`             | `Reflect.apply(receiver[selector], receiver, args)`        |
| 164 | `rawPerformNew:`              | `Reflect.construct(receiver, args)`                        |
| 166 | `rawPerformInstanceOf`        | `receiver instanceof constructor`                          |
| 167 | `rawPerformHas`               | `Reflect.has(receiver, selector)`                          |

Every `perform*` primitive catches JS-side exceptions, pushes the JS
exception object onto the stack as an alien, and returns failure. The
Newspeak wrappers then do `Error signal: rawPop printString` to turn the
captured JS exception into a Newspeak `Error`.

### Expats — Newspeak closures called from JS

When Newspeak code passes a closure to JS — typically as a `then:` callback
or an event listener — `rawPush:` detects `isKindOfClosure` and routes
through `pushExpat:` instead. That wraps the Newspeak closure in a JS
function recorded in `Module.aliens`:

```js
function expat() {
  for (var i = 0; i < arguments.length; i++) {
    aliens.push(arguments[i]);
  }
  Module._handle_signal(index, arguments.length, 0, 0);  // VM re-entry
  return aliens.pop();
}
```

When JS later calls that function, the JS side pushes each argument onto the
shared alien stack and calls `_handle_signal`, which transfers to the VM.
The VM looks up handle `index` in `platform actors handles` and runs that
handler. The handler is:

```newspeak
[:status :pending |
  | arguments = Array new: status. |
  status to: 1 by: -1 do:
    [:argumentIndex | arguments at: argumentIndex put: rawPop].
  rawPush: (closure valueWithArguments: arguments)]
```

It pops the JS-supplied arguments off the alien stack into a Newspeak
`Array`, runs the Newspeak closure, and `rawPush:`es the return value back
onto the stack — that's the value JS receives as the function's return.

**Expat handles are stored in a strong `List` (`platform actors handles`).
They are never garbage-collected**, and `nextExpatIndex` is monotonic.
Every `then:` or event-listener registration adds one entry. Long-running
sessions accumulate.

## 2. What round-trips, and what doesn't

### `rawPush:` is the hot path — and the smoking gun

`rawPush:` is defined as:

```newspeak
private rawPush: object = (
    (* :literalmessage: primitive: 154 *)
    object isKindOfClosure
        ifTrue: [pushExpat: object]
        ifFalse: [rawPushAlien: object index]
)
```

The `:literalmessage: primitive: 154` comment is the primordialsoup primitive
hook: the VM first attempts primitive 154 (`JS_pushValue`), and only falls
through to the Newspeak body if the primitive returns failure. Primitive 154
recognises exactly these Newspeak types:

- `SmallInteger`
- `MediumInteger` (int64 range)
- `Float64`
- `String`
- `nil`
- `true`
- `false`

For each, it pushes the corresponding JS native value onto the stack. For
anything else, it fails, and the Newspeak fallback fires. The fallback
expects either a closure (→ expat) or **something that responds to
`index`** — i.e. an `Alien`.

This means **`rawPush:` does not know how to push a Newspeak collection,
because a `List` / `Array` / `Map` / `Set` has no `index` method**. It
fails with a do-not-understand on `index`:

> `MNU do: in storeCachedModels:. tuples in [HTMLElement | List | …]`

That symptom does not always say "MNU on index" directly — the bridge can
produce confusing downstream effects depending on where the failure
unwinds. The 2026-05-28 incident saw it as a downstream then-callback
receiving the previous `peek` value (an HTMLElement); the immediate failure
was the DNU on `index`.

### Round-trip cheat sheet

| Type passed Newspeak → JS                        | Round-trips? | Notes |
|--------------------------------------------------|--------------|-------|
| `SmallInteger`, `MediumInteger` (int64 range)    | ✅           | JS number; may come back as `Float` if > INT32_MAX |
| `Float64`                                        | ✅           | JS number |
| `String`                                         | ✅           | UTF-8 marshalled both ways |
| `nil`                                            | ✅           | JS `null` |
| `true` / `false`                                 | ✅           | JS `true` / `false` |
| `Alien` (already wrapping a JS value)            | ✅           | Pushed by its `index` |
| Newspeak closure (`[...]`)                       | ✅ as expat | Becomes a JS function — see expat lifetime |
| Newspeak `Array` (`{...}`)                       | ❌           | No `index` slot → DNU |
| Newspeak `List`, `Map`, `Set`                    | ❌           | Same — no `index` slot |
| Any other Newspeak object without an `index`     | ❌           | Same |

| Type returned JS → Newspeak                      | What you get |
|--------------------------------------------------|--------------|
| JS `number` exactly representable as int32       | Newspeak `Integer` |
| JS `number` not exactly representable as int32   | Newspeak `Float` |
| JS `string`                                      | Newspeak `String` (UTF-8) |
| JS `null`                                        | Newspeak `nil` |
| JS `true` / `false`                              | Newspeak `true` / `false` |
| JS `undefined`                                   | `Alien withIndex: 0` — **NOT `nil`** (see §3) |
| Anything else (object, array, function, …)      | An `Alien` |

The big practical consequences:

- **You cannot return a Newspeak `List` from a `then:` callback.** The
  expat handler will try to `rawPush:` it and the bridge throws. Build a
  JS array (e.g. `JSON parse: '[]'` then `push:` items) and return that —
  or return a JS primitive — or return an `Alien` — or just side-effect
  before returning and resolve with `nil` / a sentinel.
- **You cannot pass a Newspeak `Array` literal directly as a JS function
  argument.** Same mechanism — `rawPush:` runs on each arg-push, and
  Newspeak `{a. b. c.}` is a Newspeak `Array`. Build a JS array if you
  need to pass one across.
- **You CAN pass a Newspeak closure** — the bridge wraps it as an expat.
  This is the basis of every event listener and Promise callback.

## 3. JS `undefined` is not Newspeak `nil`

When `_JS_peekAlien` finds `undefined` at the top of the stack, it pops it
and returns 0:

```c
if (undefined === aliens[lastIndex]) {
  aliens.pop();
  return 0;
}
```

Index 0 is the singleton `js undefined`. So `(somealien at: 'doesNotExist')`
returns the `undefined` alien, **not** Newspeak `nil`. Practical
consequences:

- `(alien at: 'missing') isNil` is **false** — the receiver is a real alien
  object with `isNil ^false` (inherited from Object).
- `(alien at: 'missing') isUndefined` is **true** — `Alien>>isUndefined ^0
  = index`.
- `safeStringAt:field:` in the AI code uses the `[v, ''] on: Exception` trick
  to coerce: a real `String` survives the empty-string concat; `undefined`
  raises and gets normalised to `nil`. This is why the chat code is full of
  that idiom.
- The literal value JS `null` (e.g. an explicit `null` JSON property) does
  come back as Newspeak `nil` — that path is in `JS_popValue` type -1.

## 4. JS getters and setters

`at:` is `Reflect.get(receiver, key)` and `at:put:` is `Reflect.set(receiver,
key, value)`. Both invoke JS-defined getters and setters faithfully. The
catch reported empirically in the 2026-05-18 notes:

> JS getters (`response.ok`, `response.status`) are not reliably invoked by
> `at:` *or* unary message sends through primordialsoup's alien bridge.
> Functional properties (`response.json()`, `response.text()`) work via
> unary sends.

Looking at the C++ primitives, **`Reflect.get` and `Reflect.set` themselves
do call accessor descriptors** (that's their contract). The empirical
unreliability is therefore likely a function of how specific JS implementors
expose host-object accessors — `Response.prototype.ok` is a getter on the
`Response.prototype`, and depending on engine quirks the field access can
be skipped or yield stale values when invoked via Reflect on a non-own
property. The safe rule remains:

- For **method-shaped JS members** (returns when invoked as a function), use
  Newspeak unary or keyword message sends — `response json`, `response
  text`, `arr push: x`, `localStorage setItem: k to: v`. These go through
  `Reflect.apply` and reliably trigger function semantics.
- For **plain data properties** (own properties of the object you have),
  `at:` is reliable.
- For **getters defined on a prototype chain** (e.g. `Response.prototype.ok`),
  treat the read as suspect; if it's a status-like value, find an alternative
  path that goes through a function call. The `safeAt:field: 'status'`
  pattern works for numeric status; the `'ok'` boolean did not — verify
  empirically per call.

`at:put:` returns the value that was stored (because `_JS_performSet`
pushes the argument, not the boolean from `Reflect.set`). That's the
standard Smalltalk convention, but worth remembering — you don't get the
`Reflect.set` boolean.

## 5. Method invocation: keyword selectors collapse to JS selectors

`Alien>>doesNotUnderstand:` (the entire dispatch path for `someAlien foo`,
`someAlien foo: x`, `someAlien foo: x bar: y`) does:

```newspeak
jsSelector:: asJSSelector: message selector.
```

…where `asJSSelector:` strips everything after the first colon:

```newspeak
'setItem:to:'   →   'setItem'
'addEventListener:action:' → 'addEventListener'
```

So `alien setItem: 'k' to: 'v'` becomes JS `alien.setItem('k', 'v')`. The
**second and subsequent Newspeak keyword names are discarded** — the
arguments are passed positionally. Naming the second keyword anything that
reads well for the call site is just style:

```newspeak
localStorage setItem: 'theme' to: 'dark'    "JS: localStorage.setItem('theme', 'dark')"
localStorage setItem: 'theme' value: 'dark' "same JS call; just renaming locally"
```

`#new` is the one special case — `someAlien new` and `someAlien new: x …`
call `Reflect.construct` (i.e. `new someAlien(...)`) rather than
`Reflect.apply` on a method named `new`.

A zero-arg selector beginning with `isKindOf` is short-circuited in
Newspeak — it never crosses the bridge and always returns `false`. That
guarantees `(somealien isKindOfTYPE)` is well-defined for any TYPE without
asking JS about it; subclass-overrides (like `isKindOfClosure ^false`,
`isKindOfImage ^instanceOf: HTMLImageElement`) opt in.

## 6. Promise then: the hazard zone

This is documented in detail in `NEWSPEAK_JS_PROMISE_NOTES_2026-05-18.md`.
Short version: if a Newspeak closure passed to `(jsPromise) then: [...]`
raises a Newspeak exception, control unwinds before the expat handler's
`rawPush:` runs. JS then sees the expat as having "returned" whatever
happened to be left on top of the alien stack — typically the value the
*previous* peek or push left there, often `document.documentElement` because
`window` is alien 4 and `window.document.documentElement` is a one-hop walk
that the surrounding code did. **The chain proceeds as if the raise had
been a successful return with bogus data.**

The discipline:

1. **Never let a Newspeak exception escape a `then:` closure passed to a
   JS Promise.** Wrap the body in `[ … ] on: Exception do: [:e | (global
   at: 'Promise') reject: …]`.
2. **For deliberate failures, return `Promise.reject(reason)` rather than
   raising.** A+ flattening propagates this cleanly to the next `onError:`.
3. **Keep the chain flat.** Returning `response json` from a `then:`
   callback (and letting the caller chain another `then:` on it) is the
   proven pattern in `complete:`. Nesting `response json then: [body | …]`
   inside the outer `then:` adds an extra unwind hop that has historically
   been brittle; mirror the `complete:` shape unless you specifically want
   the nested form.
4. **Don't return a Newspeak `List`/`Array` from a `then:` callback.** See
   §2 — `rawPush:` will throw on it.

## 7. Constructing JS objects: prefer `JSON parse:` to `Object new`

`(global at: 'Object') new` empirically returns handles that don't always
accept subsequent dynamic property writes the same way as ordinary JS
objects do. The convention in the AI module is:

```newspeak
createJSObject ^ <Alien> = ( ^JSON parse: '{}' )
createJSArray  ^ <Alien> = ( ^JSON parse: '[]' )
```

These return ordinary parsed JSON values that `at:put:` and array `push:`
work on cleanly. Use them as your factory.

## 8. Exception propagation in both directions

**JS exception → Newspeak.** Each `_JS_perform*` primitive wraps its
`Reflect.*` call in a `try { … } catch (exception)` that pushes the JS
exception onto the alien stack and returns failure. The Newspeak `raw*`
wrappers then raise `Error signal: rawPop printString` — i.e. you get a
Newspeak `Error` whose message is the JS exception's string. Use
`on: Exception do: [:e | …]` to handle it.

**Newspeak exception → JS** is the dangerous direction, and is the subject
of §6. The bridge does not translate a Newspeak raise into a JS throw.
Either return a `Promise.reject` explicitly, or wrap the closure body so
no raise crosses the boundary.

## 9. Expat lifetime and accumulation

Each call to `pushExpat:` (every `then:`, every event listener, every
closure-passing call into JS) does:

```newspeak
handles addLast: [:status :pending | …].
nextExpatIndex:: 1 + nextExpatIndex.
```

`handles` is `platform actors handles`, a strong `List`. Entries never go
away, and `nextExpatIndex` only grows. For a long-running chat session
with continuous tool-use loops, this is a slow leak — bounded by how many
unique callback registrations you make. It is not currently a practical
problem in the IDE, but mass-registering closures inside a hot loop will
accumulate.

There is no public API to release an expat handle. If reuse becomes
necessary, it has to go into `JSForPrimordialSoup.ns`.

## 10. Diagnostic signatures

You're hitting an alien-bridge bug if you see any of:

- A `then:` callback fires with a value that obviously did not come from
  the chain's prior step (e.g. `document.documentElement` where you
  expected a JSON response, or an alien wrapping the `Math` global). →
  Newspeak exception escaped a then-closure (§6).
- An `MNU` on `index` for a Newspeak collection inside what looks like
  the bridge layer (`rawPush:`, `storeCachedModels:`, anywhere downstream
  of a `then:` whose closure returned a `List`). → Returning a
  non-bilingual Newspeak value across the bridge (§2).
- `'Exception in turn without resolver'` in the console. → A raise was
  caught by `EventualSend>>deliver`'s backstop because no Newspeak
  resolver was wired — usually a then-closure raise that
  `Promise.reject` should have handled.
- `at:` returning `undefined`-aliens where you expected `nil`s. → JS
  `undefined` vs Newspeak `nil` (§3).
- A JS getter you're sure exists returning unexpected values when read via
  `at:`. → Getter unreliability (§4); try a method form instead.

## 11. Where to look in the source

- `primordialsoup/vm/primitives.cc` lines 3100–3500 — the EM_JS primitive
  bodies and their C++ Newspeak-VM trampolines. The full bridge protocol
  is ~400 lines of code.
- `primordialsoup/vm/main_emscripten.cc` — the initial alien table seed
  and the entry-point glue.
- `primordialsoup/newspeak/JSForPrimordialSoup.ns` — the `Alien` class.
  ~190 lines; every method here is one of: `at:`, `at:put:`, `perform`-
  family, `doesNotUnderstand:`, expat machinery, or a raw primitive
  trampoline.
- `primordialsoup/newspeak/ActorsForPrimordialSoup.ns` — `handles` lives
  here; this is the `_handle_signal` dispatch target.
- `primordialsoup/newspeak/JSTesting.ns` — the existing alien tests
  (Math, Object, undefined, integer, eval, string). Does NOT cover
  collections-across-the-bridge, Promise then-pathology, getters,
  expat behaviour, or large integers.
- The runnable workspace at `ALIENS_WORKSPACE_2026-05-28.md` (this
  directory) demonstrates every case in this document with paste-ready
  snippets.

## 12. Open questions and next moves

- **Worth fixing in the bridge?** The §6 then-pathology specifically
  could be addressed by wrapping expat-handler dispatch in
  `on:Exception do:` and converting raises into `Promise.reject` calls
  *only when the expat is being invoked from a JS Promise*. The trick is
  detecting that context. Not trivial; not in scope here.
- **Should `rawPush:` raise a clearer error on a non-bilingual receiver?**
  Yes — `object index` currently DNUs from inside an alien-bridge call,
  which surfaces in confusing places. A guard `rawPush:` that checks
  `(object isKindOfAlien or: [object isKindOfClosure])` and raises a
  descriptive Error would be a low-cost, high-value patch.
- **An expat-release API would help long-running apps.** Currently
  `handles` only grows.

These are upstream improvements to consider but they aren't blocking the
chat application layer — the discipline documented above is sufficient if
followed consistently.
