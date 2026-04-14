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

### Namespace Type Access - IMPLEMENTED ✓

**Status:** Namespace type access is now fully implemented and working.

**Implementation:**
- Modified `type:at:` to handle namespace lookups gracefully (returns nil instead of throwing NotFound)
- Completely rewrote `unaryTypeOpNode:` to properly handle member access:
  - Uses `operand at: selector` to get the member's FunctionType signature
  - Extracts the return type from the signature's range
  - Handles class side to instance side conversion when needed
  - Supports multi-step paths like `Outer Inner NestedInner`

**Test Results:**
- All 5 namespace type tests passing (170/172 total tests passing)
- Tests verify:
  - Basic namespace type access (`<NewspeakASTs MethodAST>`)
  - Types as parameters and return values
  - Types in local variables
  - Subtype relationships between namespace types

**Test Coverage:**
- `testNamespaceTypeCollectionsList` - uses `<NewspeakASTs MethodAST>`
- `testNamespaceTypeCollectionsSet` - uses `<NewspeakASTs ClassAST>`
- `testNamespaceTypeAsParameter` - namespace types as parameters
- `testNamespaceTypeInLocalVariable` - namespace types in locals
- `testNamespaceTypeSubtyping` - MethodAST subtype of AST

**Note on Collections:**
The original intent was to test with `<Collections List>`, but Collections is not present in the test manifest namespace (which only contains 17 entries from `manifest_namespace select: [:e | e isKindOfBehavior]`). The tests now use NewspeakASTs which is available in the test manifest. This may indicate that the full production build includes more types in the manifest than the test environment.

**Files Modified:**
- NewspeakTypechecker.ns:1969-1995 (type:at: method, namespace lookup)
- NewspeakTypechecker.ns:1210-1240 (unaryTypeOpNode:, member access with signatures)
- NewspeakTypecheckerTesting.ns:464-487 (NamespaceTypeTestClass)
- NewspeakTypecheckerTesting.ns:1680-1713 (namespace type tests)

## Future Enhancements

(Add future enhancements here as they come up)
