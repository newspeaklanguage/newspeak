# Newspeak Typechecker TODO

## Known Issues

### Internal Type Names Accessible to User Code

**Issue:** The internal type names `_Array` and `_Object` are currently accessible to user code, but should not be. Only the public names `Array` and `Object` should be available.

**Current Status:**
- Tests added: `testUnderscoreArrayNotAccessible` and `testUnderscoreObjectNotAccessible`
- Both tests currently fail (165/167 tests passing)
- Located in: NewspeakTypecheckerTesting.ns

**Root Cause:**
- The kernel classes are actually named `_Object` and `_Array` internally
- When the typechecker generates type paths via `selfIdAST` (NewspeakTypechecker.ns:654-664), it uses the mixin's real name
- These generated type identifiers are resolved through `type:at:` which needs to recognize `_Object` and `_Array`
- No mechanism exists to distinguish typechecker-generated AST nodes from user-written ones

**Possible Solutions:**
1. Rename the actual kernel classes from `_Object` to `Object` and `_Array` to `Array`
2. Modify `selfIdAST` to translate internal names to public names when generating type paths
3. Add a mechanism to distinguish typechecker-generated AST nodes from user-written ones (e.g., a flag on AST nodes)

**Files Involved:**
- NewspeakTypechecker.ns:133 (objectMixin initialization)
- NewspeakTypechecker.ns:166 (arrayMixin initialization)
- NewspeakTypechecker.ns:637-664 (path and selfIdAST methods)
- NewspeakTypechecker.ns:1964-1966 (type:at: mappings for _Object and _Array)

### Namespace Type Access Not Fully Implemented

**Issue:** The typechecker should support accessing types from the global namespace (e.g., `<Collections>`) and nested types from namespace modules (e.g., `<Collections List>`), but this functionality is only partially implemented.

**Current Status:**
- Tests added: 5 tests for namespace type access in NewspeakTypecheckerTesting.ns
  - `testNamespaceTypeCollectionsList`
  - `testNamespaceTypeCollectionsSet`
  - `testNamespaceTypeAsParameter`
  - `testNamespaceTypeInLocalVariable`
  - `testNamespaceTypeSubtyping`
- Test results: 166/172 passing (4 namespace tests failing, 2 _Array/_Object tests failing)
- Fixed: Namespace lookup no longer throws `NotFound` errors (was causing crashes)
- Remaining issue: Nested type access like `<Collections List>` doesn't find `List` within `Collections`

**Root Cause:**
- Top-level namespace lookup works: `Collections` is found in the namespace
- Nested class lookup fails: `List` is not found as a nested class within `Collections`
- Architectural issue: In Newspeak's module system, `Collections` is a module factory, and `List` is accessed through the module instance (`platform collections List`), but may not be a nested class in the traditional sense
- The existing source code contains `<Collections List>` syntax but it was never tested (see commented-out lines 17-19 in NewspeakTypecheckerTesting.ns)

**What Works:**
- Simple namespace types: types defined at the top level of the namespace can be referenced
- Namespace lookup: `type:at:` now properly handles namespace lookups without throwing errors

**What Doesn't Work:**
- Nested type access: `<Collections List>` style syntax for accessing types within namespace modules
- Module member access: The typechecker needs to understand how to navigate from a module class to its exported types

**Next Steps:**
1. Determine the correct semantics for namespace type qualification in Newspeak
2. Decide whether `<Collections List>` should look for a nested class or use a different mechanism
3. Consider if modules need special handling in the type system
4. May require changes to how modules expose their types to the typechecker

**Files Involved:**
- NewspeakTypechecker.ns:1969-1995 (type:at: method, namespace lookup)
- NewspeakTypechecker.ns:1210-1226 (unaryTypeOpNode:, nested type resolution)
- NewspeakTypechecker.ns:2008-2028 (localMember:in:, nested class lookup)
- NewspeakTypecheckerTesting.ns:463-492 (NamespaceTypeTestClass and tests)

## Future Enhancements

(Add future enhancements here as they come up)
