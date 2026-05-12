# Session Summary: AI Access for the Newspeak IDE

**Date:** 2026-05-10
**Branch:** `webide-ai-access`
**Commit:** e8ce8cc

## Overview

This session established the foundation for AI model integration in the Newspeak web IDE. The design enables bidirectional communication: a human user can chat with an AI from within the IDE (with the IDE automatically providing context), and the AI can query the IDE via tool use (function calling) to retrieve class source, find senders/implementors, etc.

## Architecture

The system is decomposed into three modules with increasing specificity:

```
AIAccess (general-purpose)
    └── AIChatUI (general-purpose UI)
            └── AI_IDE_Support (IDE-specific)
```

### Module 1: AIAccess.ns — AI Infrastructure

**Factory:** `AIAccess usingPlatform: platform`

General-purpose module providing AI model access from any Newspeak application. No IDE dependency.

**Key classes:**

- **`Tool`** — Defines a tool the AI may invoke. Fields: `name`, `description`, `inputSchema` (JSON Schema string), `handler` (block `[:input <Alien> | ^String]`).

- **`Provider`** — Abstract class. Subclass and implement `complete:system:tools:maxTokens:` to support a new AI backend. Returns a JS Promise resolving to a response object with `content` (array of blocks) and `stop_reason`.

- **`AnthropicProvider`** — Concrete provider for Claude. Factory: `apiKey:model:`. Calls the Anthropic Messages API directly from the browser using the `anthropic-dangerous-direct-browser-access: true` header. No proxy server needed. The "bring your own API key" pattern — users supply their own key, stored in their browser.

- **`Session`** — Manages a multi-turn conversation with tool use. Key design:
  - `apiMessages` — full API message history including internal tool_use/tool_result rounds
  - `completeWithToolLoop` — recursive promise-based loop: sends messages → receives response → if tool_use, executes tool handlers and sends results → repeats until final text
  - `displayMessages` — extracts clean user/assistant text pairs for UI display, filtering out tool machinery
  - `sendMessage: text` — public API, returns a JS Promise resolving to the assistant's final text

**JS interop pattern:** Uses PrimordialSoup's Alien FFI. JS objects created via `JSON parse: '{}'`. Properties accessed via `at:`/`at:put:`. Promises chained via `then:`. Blocks passed as JS callbacks are automatically wrapped by the Alien mechanism.

### Module 2: AIChatUI.ns — Chat User Interface

**Factory:** `AIChatUI usingPlatform: platform aiAccess: ai`

General-purpose Hopscotch chat UI. Any application (not just the IDE) can use this.

**Key classes:**

- **`AIChatSetupSubject`** — Setup screen for entering an API key. Model is a **provider class** (e.g., `AnthropicProvider`). The class name drives the localStorage key for persisting the API key (`'ns_ai_apikey_', model name`). Designed for subclassing:
  - `createProvider` — creates a provider instance from the API key and model name; calls `model apiKey: apiKey model: modelName`
  - `createSession: provider` — creates a Session with no tools; **override this in subclasses to add tools**
  - `startChat` — orchestrates: validates key, persists to localStorage, creates provider, creates session, returns a `ChatSubject`

- **`AIChatSetupPresenter`** — Renders the setup form: API key field, model name field, error display, and "Start Chat" button. On start, navigates to the ChatSubject.

- **`ChatSubject`** — Model for an active chat conversation. Factory: `onModel:` (standard Subject protocol). Model is a Session. State: `draft` (current input text), `waiting` (boolean), `errorMessage`. The `sendDraft` method returns the JS Promise so the presenter can handle async completion.

- **`ChatPresenter`** — Renders the chat: heading with Clear button, scrollable messages area, CodeMirror input editor. Uses the editor's `acceptResponse:` callback (accept button / keyboard shortcut) to send messages — no separate Send button. Async flow: `respondToSend` calls `updateGUI:` to send the draft, then chains `then:onError:` on the returned Promise to update UI on completion.

**Async UI pattern:** All `updateGUI:` calls happen from the Presenter (which has access to the Hopscotch shell), never from the Subject. The Subject is a pure state holder. Promise callbacks from the `then:onError:` on the JS promise trigger `updateGUI:` to refresh the view.

### Module 3: AI_IDE_Support.ns — IDE Integration

**Factory:** `AI_IDE_Support usingPlatform: platform ide: webIde aiAccess: aiAccessModule chatUI: chatUIModule`

IDE-specific module following the standard `usingPlatform:ide:` pattern. Parameterized by the IDE instance and the two general-purpose AI modules.

**Responsibilities:**

1. **Re-exports AI classes** for use by other IDE modules: `Tool`, `Provider`, `AnthropicProvider`, `Session`, `ChatSubject`. Other IDE presenters access these via `ide aiSupport`.

2. **Defines 7 IDE query tools** that the AI can invoke:

   | Tool | Description |
   |------|-------------|
   | `get_class_source` | Full source of a class; supports dotted paths for nested classes (e.g., `"Outer.Inner"`) |
   | `get_method_source` | Source of a method by selector; supports instance/class side |
   | `get_class_header` | Class header only (factory, superclass, slots) |
   | `list_class_members` | Structured listing of all members with access modifiers |
   | `senders_of` | All methods sending a given selector |
   | `implementors_of` | All implementors of a given selector |
   | `search_classes` | Search all classes (including nested) by name substring |

   Tools use the mirror API (`ClassMirror`, `MixinMirror`, `MethodMirror`, etc.) and the `systemScope` from `Namespacing` for senders/implementors queries.

3. **`IDEChatSetupSubject`** — Subclass of `AIChatSetupSubject` that overrides `createSession:` to include the IDE tools. This is what the home page "AI Chat" link creates.

4. **Convenience methods:**
   - `createSessionWithProvider:` — creates a Session pre-loaded with IDE tools
   - `createChatWithProvider:` — creates a ChatSubject with an IDE-tooled session

**Class path resolution:** The `resolveClassPath:` helper splits dotted paths (e.g., `"Foo.Bar.Baz"`) using `findTokens: '.'` and navigates from Root through nested classes.

## IDE Wiring (HopscotchWebIDE.ns changes)

The outer `packageUsing:` class imports the three new modules from the manifest:
```
private AIAccess = manifest AIAccess.
private AIChatUI = manifest AIChatUI.
private AI_IDE_Support = manifest AI_IDE_Support.
```

The inner `HopscotchWebIDE usingPlatform:` class instantiates them in dependency order:
```
private theAIAccess = AIAccess usingPlatform: p.
private theAIChatUI = AIChatUI usingPlatform: p aiAccess: theAIAccess.
public aiSupport = AI_IDE_Support usingPlatform: p ide: self aiAccess: theAIAccess chatUI: theAIChatUI.
```

All three are registered in both `populateNamespaceUsingPlatform:` and `namespaceGivenPlatform:` so they're available in the IDE namespace for browsing and workspace access.

## IDE Wiring (Browsing.ns changes)

HomePresenter gains:
- `navigateToAIChat` — creates `IDEChatSetupSubject onModel: ide aiSupport AnthropicProvider` and enters it
- An "AI Chat" link in the home page's third column, alongside "Newspeak Source" and "Workspaces"

## Transport: Direct Browser API Access

The Anthropic API is the only major AI provider that supports direct browser access (via the `anthropic-dangerous-direct-browser-access: true` header). OpenAI and Google Gemini do not support CORS and would require a proxy server.

The `Provider` abstraction allows adding new backends. A proxy-based OpenAI provider or a local model provider (Ollama) would just be additional `Provider` subclasses.

## Key Design Decisions

1. **Provider class as model for setup:** `AIChatSetupSubject`'s model is the provider *class* itself (e.g., `AnthropicProvider`). This provides both the factory for creating instances (`model apiKey: k model: m`) and a name for the localStorage key (`model name`). Different providers get different storage keys automatically.

2. **Session creation is overridable:** `createSession:` is a separate method so `IDEChatSetupSubject` can override it to inject tools. The base class creates sessions with no tools.

3. **Separation of concerns:** AIAccess and AIChatUI have no IDE dependency. AI_IDE_Support bridges them to the IDE. This means AI functionality could be used in non-IDE Newspeak applications.

4. **No MCP yet:** The tool-use protocol uses the AI model's native function calling rather than MCP. MCP could be layered on later if interoperability with other MCP clients/servers is needed.

5. **Async handled in Presenter:** Promise callbacks call `updateGUI:` from the Presenter, not the Subject, because only Presenters/Fragments have access to the Hopscotch shell's refresh machinery.

## Newspeak Syntax Lessons Learned

1. **Nested classes before methods:** In a Newspeak class body, all nested class declarations must precede all method declarations.
2. **`::` only for self sends:** The `::` setter syntax is for implicit receiver (self) sends only. For explicit receivers, use the regular keyword send `:` (e.g., `subject draft: value`, not `subject draft:: value`).
3. **`Error signal:` not `error:`:** Newspeak signals errors with `Error signal: 'message'`.
4. **`Color` is in `platform graphics`**, not `platform hopscotch`.
5. **`findTokens:` for string splitting**, not `splitBy:` or `splitOn:`.
6. **`includesSubstring:` exists** in KernelForPrimordialSoup.
7. **Always validate with `tool/parse-validate.sh`** after writing Newspeak code.

## Current Status

- All files parse and build successfully
- The IDE starts with the AI Chat link on the home page
- Clicking "AI Chat" shows the setup screen
- API key is persisted in localStorage across sessions
- Basic chat with Claude works end-to-end
- IDE tools are registered but not yet tested (require sending a query that triggers tool use)

## Next Steps

Potential areas for future work:

- **Test IDE tools end-to-end:** Ask the AI questions that trigger tool use (e.g., "Show me the source of class CounterUI")
- **Embed chat in IDE views:** Add ChatSubject to method presenters, class presenters, object inspectors, etc., with automatic context
- **IDE manipulation tools:** Let the AI open presenters, navigate to classes, modify code via builders
- **Evaluation tool:** Let the AI evaluate Newspeak expressions in a context (async, uses ThreadMirror)
- **Multiple providers:** Add proxy-based OpenAI provider, local model support
- **MCP support:** Layer MCP protocol for interoperability
- **System prompt enhancement:** Include Newspeak language description, coding conventions, and current context in the system prompt
- **Streaming responses:** Use SSE/streaming for real-time display of AI responses
