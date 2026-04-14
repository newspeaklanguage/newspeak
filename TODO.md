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

## Future Enhancements

(Add future enhancements here as they come up)
