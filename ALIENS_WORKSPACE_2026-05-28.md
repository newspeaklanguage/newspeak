# Runnable workspace snippets — alien behaviour and gotchas

Companion to `ALIENS_NOTES_2026-05-28.md`. Each snippet is a self-contained
workspace expression you can paste into an IDE workspace and Evaluate
(`platform`, `ide`, `aliens`, `collections`, etc. are in scope on every
workspace by inheritance from `Workspace`). Expected output is shown after
each snippet — anything else is a bug or a behaviour change worth
documenting.

A few snippets demonstrate the **failure modes** documented in the notes;
those are marked **❌ DOES NOT WORK** and either throw, hang, or produce
nonsense. Run them so you've seen the failure shape with your own eyes.

## Setup convention

These snippets use a few short forms for readability. If a workspace is
fresh, evaluate the setup line first, then any snippet below:

```newspeak
| js global Math Object JSON Promise |
js:: platform js.
global:: js global.
Math:: global at: 'Math'.
Object:: global at: 'Object'.
JSON:: global at: 'JSON'.
Promise:: global at: 'Promise'.
```

(Newspeak workspaces let you define top-level temporaries via `| … |`.)

If you'd rather one-line each snippet, replace `Math` with `(platform js
global at: 'Math')` etc. throughout — the patterns are the same.

## 1. The alien table — fixed and dynamic indices

### 1a. Pre-allocated indices

```newspeak
js undefined index.    "→ 0"
js undefined isUndefined.  "→ true"

(js global at: 'window') == js global.  "→ true — window IS index 4"

"undefined != nil — different objects"
js undefined isNil.    "→ false"
js undefined == nil.   "→ false"
nil isUndefined.       "MNU on Newspeak nil — only Alien answers isUndefined"
```

### 1b. The `undefined`-collapsing peek

```newspeak
| obj |
obj:: JSON parse: '{}'.
(obj at: 'doesNotExist') index.       "→ 0 — collapsed to js undefined"
(obj at: 'doesNotExist') isUndefined. "→ true"
(obj at: 'doesNotExist') isNil.       "→ false — it's an Alien, not nil"
```

That last line is the classic surprise: reading a missing property gives you
the `undefined` alien (`Alien withIndex: 0`), which answers `isNil ^false`
because it inherits from Object. Always use `isUndefined` (or
`safeStringAt:`-style coercion) when probing JS objects.

### 1c. JS `null` is Newspeak `nil`

```newspeak
global eval: 'null'.   "→ nil (Newspeak)"
nil = (global eval: 'null').  "→ true"
nil class.   "→ UndefinedObject"
```

So `null` and `undefined` lose their JS distinction on the way over: `null`
becomes `nil`, but `undefined` becomes the `Alien withIndex: 0` singleton.

## 2. Round-trip: what crosses the bridge

### 2a. Numbers

```newspeak
global eval: '42'.       "→ 42 (SmallInteger)"
global eval: '42.5'.     "→ 42.5 (Float)"
global eval: '2147483647'. "→ 2147483647 (Integer; INT32_MAX)"
global eval: '2147483648'. "→ 2147483648.0 (Float — past INT32_MAX comes back as Float)"
global eval: '-2147483648'. "→ -2147483648"
global eval: '-2147483649'. "→ -2147483649.0 (Float)"
```

The `(0 | alien) === alien` check in `_JS_peekType` is what classifies
something as Integer (-4) vs Float (-5); anything outside int32 range is
reported as Float on the way back, even though the underlying JS value is
exact.

### 2b. Strings

```newspeak
global eval: '"hello"'.   "→ 'hello'"
global eval: '"héllo 🌍"'. "→ 'héllo 🌍' (UTF-8 round-trips)"
'hello' size.              "→ 5 (Newspeak side)"
```

### 2c. Booleans, nil

```newspeak
global eval: 'true'.   "→ true"
global eval: 'false'.  "→ false"
global eval: 'null'.   "→ nil"
```

### 2d. Aliens going through methods

```newspeak
| obj |
obj:: JSON parse: '{"a":1,"b":2}'.
obj at: 'a'.       "→ 1"
obj at: 'b'.       "→ 2"
obj at: 'c' put: 3.
obj at: 'c'.       "→ 3"
(obj removeKey: 'c').  "→ true (Reflect.deleteProperty success)"
(obj at: 'c') isUndefined.  "→ true"
```

### 2e. Closures as expats

```newspeak
| arr doubled |
arr:: JSON parse: '[1, 2, 3, 4, 5]'.
doubled:: arr map: [:n | n * 2].   "JS .map invokes Newspeak closure as expat"
doubled at: 0.                      "→ 2"
doubled at: 4.                      "→ 10"
```

The block `[:n | n * 2]` is registered as a JS function (an expat) and
fired by JS `Array.prototype.map`. Each invocation pushes the JS args onto
the alien stack, transfers to the VM, runs the Newspeak closure, and pushes
the return value back. Numbers round-trip cleanly so this Just Works.

## 3. ❌ DOES NOT WORK: returning a Newspeak collection across the bridge

### 3a. From a Promise then-callback

```newspeak
| Promise p |
Promise:: global at: 'Promise'.
p:: Promise resolve: 'ignored'.

"This blows up — the then-callback's return value is a Newspeak List, and
 rawPush: does not know how to push it."
p then: [:_ | platform collections List new ].

"Expected: an alien-bridge failure (DNU on `index`, or a confusing
 downstream symptom depending on what happens next on the alien stack)."
```

The Newspeak List has no `index` slot. `rawPush:` falls past primitive 154
(which doesn't recognise List), is not a closure, and tries `object index`
on it. DNU. This is the 2026-05-28 incident in miniature.

### 3b. From a JS method call expecting an array

```newspeak
| arr |
arr:: JSON parse: '[]'.

"This passes a Newspeak Array, which is NOT a JS array. rawPush: throws."
arr concat: { 1. 2. 3. }.

"The fix: build a JS array."
arr concat: (JSON parse: '[1, 2, 3]').   "→ a new JS array with [..., 1, 2, 3]"
```

The literal `{ 1. 2. 3. }` is a *Newspeak* Array, not a JS array. Same
issue as 3a — no `index` slot, no closure, `rawPush:` fails.

### 3c. The fix: build a JS array

```newspeak
| arr js_arr |
js_arr:: JSON parse: '[]'.
{1. 2. 3.} do: [:n | js_arr push: n].
js_arr at: 'length'.    "→ 3"
js_arr at: 0.           "→ 1"
JSON stringify: js_arr. "→ '[1,2,3]'"
```

Use the Newspeak collection to drive iteration, push individual numbers
(which round-trip) onto a JS array. **Never let the Newspeak collection
cross the boundary as a value.**

## 4. ❌ DOES NOT WORK: raising inside a then-closure

### 4a. The pathology

```newspeak
| Promise p |
Promise:: global at: 'Promise'.
p:: Promise resolve: 'hello'.

"This raise unwinds before the expat's rawPush: runs.
 JS sees the then-callback as having returned whatever was on top of
 the alien stack — typically something unrelated."
(p then: [:v | Error signal: 'boom']) then: [:next |
    (* next is NOT 'hello', and is NOT a rejection — it's stale alien data *)
    next class printString out.
].
```

Expected: a confusing console line printing the class of something you did
not put on the alien stack. You will not see a Promise rejection or
`onError:` firing. The original 'boom' message is gone.

### 4b. The fix: return a rejected Promise

```newspeak
| Promise p |
Promise:: global at: 'Promise'.
p:: Promise resolve: 'hello'.

(p then: [:v | Promise reject: 'boom']) onError: [:reason |
    'rejected with: ', reason out.
].
```

Expected: `'rejected with: boom'` appears in console. A+ flattening
propagates the explicit rejection cleanly.

### 4c. The defensive wrap

```newspeak
| Promise p |
Promise:: global at: 'Promise'.
p:: Promise resolve: 'hello'.

(p then: [:v |
    [
        (* arbitrary body that might raise *)
        v size = 5 ifFalse: [Error signal: 'expected 5 chars'].
        v asUppercase
    ] on: Exception do: [:e |
        Promise reject: e messageText
    ]
]) then: [:upper | upper out] onError: [:reason | 'failure: ', reason out].
```

Expected: `'HELLO'`. If you change the `= 5` check to `= 6`, you get
`'failure: expected 5 chars'` — the backstop turns the raise into a clean
Promise rejection.

## 5. Getters and methods

### 5a. Plain data property (works)

```newspeak
| obj |
obj:: JSON parse: '{"name":"Ada","age":36}'.
obj at: 'name'.   "→ 'Ada'"
obj at: 'age'.    "→ 36"
```

### 5b. Method form (works for function-shaped JS members)

```newspeak
| arr |
arr:: JSON parse: '[3, 1, 4, 1, 5]'.
arr sort.            "→ the same array, mutated to [1, 1, 3, 4, 5]"
arr join: ' / '.     "→ '1 / 1 / 3 / 4 / 5'"
arr at: 'length'.    "→ 5"
```

### 5c. JS getter on a prototype (sometimes unreliable)

You need an actual JS object with a prototype-defined getter for this to
fire. The simplest in-browser one to inspect: try a `fetch` response.

```newspeak
"This is illustrative — actually firing it from a workspace requires
 wiring up a real fetch. The empirical observation from the chat code
 is that `response at: 'ok'` was unreliable; `response at: 'status'`
 worked. Verify per-call when in doubt."

"Reliable replacement for fetch's ok-flag:"
"   (status isNil or: [status >= 400]) ifTrue: [reject] ifFalse: [proceed]"
```

The point: **method forms are reliable**, **own-property data reads are
reliable**, **prototype getters are suspect**. The C++ uses `Reflect.get`
which *should* honour them, but historical reports diverge — verify
empirically.

## 6. Keyword selectors collapse to JS selectors

```newspeak
| ls |
ls:: js global at: #localStorage.

"These two calls are IDENTICAL — Newspeak keyword names after the first
 colon are stripped. The second 'to:' / 'value:' / whatever you choose
 is purely a Newspeak readability choice; the JS call is the same."
ls setItem: 'theme' to: 'dark'.
ls setItem: 'theme' value: 'dark'.
ls setItem: 'theme' AnyNewspeakKeyword: 'dark'.

"Underlying JS call in all three cases: localStorage.setItem('theme', 'dark')"
ls getItem: 'theme'.   "→ 'dark'"
ls removeKey: 'theme'. "→ true"
```

`#new` is the one exception — it calls `Reflect.construct` rather than a
method named "new":

```newspeak
| arr |
arr:: (global at: 'Array') new: 3.   "→ a JS Array with length 3"
arr at: 'length'.   "→ 3"

"vs explicit method call (different effect):"
arr fill: 0.        "→ [0, 0, 0]"
```

## 7. Closures with multiple arguments

```newspeak
| arr reduced |
arr:: JSON parse: '[1, 2, 3, 4]'.
reduced:: arr reduce: [:acc :x | acc + x] with: 100.   "JS arr.reduce(fn, 100)"
reduced.   "→ 110"
```

The Newspeak two-arg closure becomes a JS function called by `reduce` with
`(accumulator, currentValue, …)`. Newspeak ignores extra JS arguments; JS
gets whatever your closure returns, marshalled across the bridge.

## 8. Constructing JS objects: prefer JSON.parse

```newspeak
"The empirically-reliable factory:"
| obj |
obj:: JSON parse: '{}'.
obj at: 'a' put: 1.
obj at: 'b' put: 'two'.
JSON stringify: obj.   "→ '{\"a\":1,\"b\":\"two\"}'"

"The alternative (Object new) sometimes returns handles whose at:put: 
 behaves differently in edge cases — observed in AIAccess. Stick with 
 JSON.parse('{}') unless you specifically need Object.new semantics."
```

## 9. Expat handle accumulation (live measurement)

```newspeak
| before |
before:: (platform actors handles) size.

"Each then: call registers one expat handle."
1 to: 100 do: [:i |
    | p |
    p:: (global at: 'Promise') resolve: i.
    p then: [:v | v]
].

"Wait a moment for the promises to flush, then:"
(platform actors handles) size - before.   "→ ~100 — expats accumulate"
```

Confirms the §9 note: every then-callback registration leaves a permanent
trace in `platform actors handles`. For long-running sessions, monitor.

## 10. Sanity checks for adapting the IDE

Run after any change to the bridge layer:

```newspeak
"Round-trip cheats — all should return values shown."
js undefined index.                              "→ 0"
nil = (global eval: 'null').                     "→ true"
js undefined == nil.                             "→ false"
(JSON parse: '{}') at: 'missing'; isUndefined.   "→ true"
(JSON parse: '[1,2]') at: 'length'.              "→ 2"
'héllo' = (global eval: '"héllo"').              "→ true"
```

If any of these regresses, the bridge has changed and either the C++
primitives in `primordialsoup/vm/primitives.cc` or the Newspeak Alien class
in `primordialsoup/newspeak/JSForPrimordialSoup.ns` has shifted in a way
that affects the IDE.
