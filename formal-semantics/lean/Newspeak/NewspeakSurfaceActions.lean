import Newspeak.SurfaceSyntax
import Newspeak.PEGWellFormed

namespace Newspeak

/-!
# Newspeak semantic actions

The action-value sum includes both final surface nodes and the typed
intermediate values used by the grammar's folds.  Lexical decoding is a
separate, replaceable service because concrete escape/radix normalization is
specified independently of the tree projection.
-/

structure SurfacePatternDeclaration where
  span : SourceSpan
  selector : Selector
  formals : List SurfaceDeclaration
deriving Repr

structure SurfaceCodeBody where
  span : SourceSpan
  locals : Option SurfaceSlotGroup
  statements : List SurfaceStatement
deriving Repr

structure SurfaceClassHeader where
  span : SourceSpan
  locals : Option SurfaceSlotGroup
  statements : List SurfaceStatement
deriving Repr

structure SurfaceMixinTail where
  span : SourceSpan
  heads : List SurfaceInheritanceHead
  classStructure : Option SurfaceClassStructure
deriving Repr

inductive SurfaceActionValue where
  | token (text : SourceText) (span : SourceSpan)
  | name (value : String)
  | selector (value : Selector)
  | keyword (value : String)
  | access (value : Access)
  | atom (value : AtomPayload)
  | clause (value : SurfaceClause)
  | clauses (values : List SurfaceClause)
  | expression (value : SurfaceExpression)
  | pattern (value : SurfacePattern)
  | patternPair (keyword : String) (pattern : Option SurfacePattern)
  | statement (value : SurfaceStatement)
  | statements (values : List SurfaceStatement)
  | declaration (value : SurfaceDeclaration)
  | declarations (values : List SurfaceDeclaration)
  | slotGroup (value : SurfaceSlotGroup)
  | patternDeclaration (value : SurfacePatternDeclaration)
  | codeBody (value : SurfaceCodeBody)
  | classHeader (value : SurfaceClassHeader)
  | classStructure (value : SurfaceClassStructure)
  | inheritanceHead (value : SurfaceInheritanceHead)
  | mixinTail (value : SurfaceMixinTail)
  | inheritance (value : SurfaceInheritance)
  | objectHeader (value : SurfaceObjectHeader)
  | cascadeParts (initial subsequent : List SurfaceClause)
  | compilationUnit (value : SurfaceCompilationUnit)
deriving Repr

structure NewspeakLexicalDecoders where
  identifier : SourceText → Option String
  binarySelector : SourceText → Option Selector
  keyword : SourceText → Option String
  setterName : SourceText → Option String
  number : SourceText → Option AtomPayload
  stringLiteral : SourceText → Option String
  symbolLiteral : SourceText → Option String
  access : SourceText → Option Access
  mutability : SourceText → SurfaceMutability
  metadataTag : List SurfaceActionValue → String

def actionSpan (span : SourceSpan) := span

def surfaceActionToken (source : SourceText) (span : SourceSpan) :
    SurfaceActionValue :=
  .token (sourceSlice source span) span

def asSurfaceClause : SurfaceActionValue → Option SurfaceClause
  | .selector selector => some (.clause ⟨0, 0⟩ selector [])
  | .clause clause => some clause
  | _ => none

def flattenSurfaceClauses : List SurfaceActionValue → Option (List SurfaceClause)
  | [] => some []
  | .clause clause :: remaining => do
      pure (clause :: (← flattenSurfaceClauses remaining))
  | .clauses clauses :: remaining => do
      pure (clauses ++ (← flattenSurfaceClauses remaining))
  | .selector selector :: remaining => do
      pure (.clause ⟨0, 0⟩ selector [] :: (← flattenSurfaceClauses remaining))
  | _ => none

def foldExplicitMessages (receiver : SurfaceExpression) :
    List SurfaceClause → SurfaceExpression
  | [] => receiver
  | .clause span selector arguments :: remaining =>
      foldExplicitMessages (.messageSend span receiver selector arguments) remaining

def foldImplicitMessages (span : SourceSpan) :
    List SurfaceClause → Option SurfaceExpression
  | [] => none
  | .clause _ selector arguments :: remaining =>
      some (foldExplicitMessages (.implicitSend span selector arguments) remaining)

def makeSurfaceCascade (span : SourceSpan) (receiver : SurfaceExpression)
    (initial subsequent : List SurfaceClause) : SurfaceExpression :=
  if subsequent.isEmpty then foldExplicitMessages receiver initial
  else .cascade span receiver initial subsequent

def flattenSurfaceStatements : List SurfaceActionValue →
    Option (List SurfaceStatement)
  | [] => some []
  | .expression expression :: remaining => do
      pure (.expression expression.span expression ::
        (← flattenSurfaceStatements remaining))
  | .statement statement :: remaining => do
      pure (statement :: (← flattenSurfaceStatements remaining))
  | .statements statements :: remaining => do
      pure (statements ++ (← flattenSurfaceStatements remaining))
  | _ => none

def flattenSurfaceDeclarations : List SurfaceActionValue →
    Option (List SurfaceDeclaration)
  | [] => some []
  | .declaration declaration :: remaining => do
      pure (declaration :: (← flattenSurfaceDeclarations remaining))
  | .declarations declarations :: remaining => do
      pure (declarations ++ (← flattenSurfaceDeclarations remaining))
  | _ => none

def erasedNewspeakCaptures : List CaptureName :=
  ["white", "reservedWord", "idRest", "rawId", "rawKeyword",
   "keywords", "rawBinary", "metadataTag", "commentItem", "classToken",
   "lazyModifier", "outerToken"]

def erasedNewspeakTypeCaptures : List CaptureName :=
  ["returnType", "typePrimary", "typeFactor", "parenthesizedTypeExpression",
   "typeTerm", "typeExpr", "typeArguments", "tupleType", "blockArgType",
   "blockReturnType", "nonEmptyBlockArgList", "blockType", "typeFormal",
   "typeParamConstraint", "typeBoundQualifier", "inferenceClause",
   "returnTypeInferenceClause", "msgSelector", "typeArgInferenceClause",
   "TW_arg", "TW_for", "TW_generic", "TW_inheritedTypeOf", "TW_is",
   "TW_message", "TW_of", "TW_receiverType", "TW_subtypeOf", "TW_typeArg",
   "TW_where"]

def metadataNewspeakTypeCaptures : List CaptureName :=
  ["type", "typeParameterDecl", "typePattern"]

def identityNewspeakCaptures : List CaptureName :=
  ["literal", "receiverPrimary", "sendExpression", "slotDecls",
   "blockParameter", "inheritancePrefix", "patternLiteral",
   "keywordPatternValue"]

private def emitValue (value : SurfaceActionValue) :
    Option (SemanticActionResult SurfaceActionValue SurfaceMetadata) :=
  some (.emit value)

private def eraseValue :
    Option (SemanticActionResult SurfaceActionValue SurfaceMetadata) :=
  some .erase

def newspeakSurfaceAction (decoders : NewspeakLexicalDecoders)
    (name : CaptureName) (span : SourceSpan)
    (children : List SurfaceActionValue) (slice : SourceText) :
    Option (SemanticActionResult SurfaceActionValue SurfaceMetadata) :=
  if name ∈ erasedNewspeakCaptures || name ∈ erasedNewspeakTypeCaptures then
    eraseValue
  else if name ∈ metadataNewspeakTypeCaptures then
    some (.metadata ⟨"staticType", slice, span⟩)
  else if name ∈ identityNewspeakCaptures then
    match children with
    | [value] => emitValue value
    | _ => none
  else
    match name, children with
    | "id", _ => do emitValue (.name (← decoders.identifier slice))
    | "unarySelector", [.name spelling] =>
        emitValue (.selector ⟨spelling⟩)
    | "binarySelector", _ => do
        emitValue (.selector (← decoders.binarySelector slice))
    | "keyword", _ => do emitValue (.keyword (← decoders.keyword slice))
    | "setterKeyword", _ => do
        emitValue (.name (← decoders.setterName slice))
    | "selfToken", _ => emitValue (.expression (.selfValue span))
    | "superToken", _ => emitValue (.expression (.superValue span))
    | "outerReceiver", [.name receiverName] =>
        emitValue (.expression (.outer span receiverName))
    | "comment", _ =>
        some (.metadata ⟨decoders.metadataTag children, slice, span⟩)
    | "number", _ => do
        emitValue (.expression (.atom span (← decoders.number slice)))
    | "string", _ => do
        emitValue (.expression
          (.atom span (.string (← decoders.stringLiteral slice))))
    | "symbol", _ => do
        emitValue (.expression
          (.atom span (.symbol (← decoders.symbolLiteral slice))))
    | "trueToken", _ => emitValue (.expression (.atom span (.boolean true)))
    | "falseToken", _ => emitValue (.expression (.atom span (.boolean false)))
    | "nilToken", _ => emitValue (.expression (.atom span .nilAtom))
    | "binaryMessage", [.selector selector, .expression argument] =>
        emitValue (.clause (.clause span selector [argument]))
    | "keywordMessage", values => do
        let pairs ← collectKeywordArguments values
        let spelling := pairs.foldl (fun current pair => current ++ pair.1) ""
        emitValue (.clause (.clause span ⟨spelling⟩ (pairs.map Prod.snd)))
    | "message", [.selector selector] =>
        emitValue (.clause (.clause span selector []))
    | "message", [.clause clause] => emitValue (.clause clause)
    | "cascadeMessage", [.selector selector] =>
        emitValue (.clause (.clause span selector []))
    | "cascadeMessage", [.clause clause] => emitValue (.clause clause)
    | "primary", [.selector selector] =>
        emitValue (.expression (.identifier span selector.spelling))
    | "primary", [.declaration declaration] =>
        emitValue (.expression (.classExpression span declaration))
    | "primary", [.expression expression] => emitValue (.expression expression)
    | "unaryExpression", .expression receiver :: values => do
        emitValue (.expression (foldExplicitMessages receiver
          (← flattenSurfaceClauses values)))
    | "binaryExpression", .expression receiver :: values => do
        emitValue (.expression (foldExplicitMessages receiver
          (← flattenSurfaceClauses values)))
    | "keywordExpression", .expression receiver :: values => do
        emitValue (.expression (foldExplicitMessages receiver
          (← flattenSurfaceClauses values)))
    | "eventualExpression", [.expression receiver, .clause (.clause _ selector args)] =>
        emitValue (.expression (.eventualSend span receiver selector args))
    | "implicitKeywordSend", [.clause (.clause _ selector args)] =>
        emitValue (.expression (.implicitSend span selector args))
    | "nontrivialUnaryMessages", values => do
        emitValue (.clauses (← flattenSurfaceClauses values))
    | "nontrivialBinaryMessages", values => do
        emitValue (.clauses (← flattenSurfaceClauses values))
    | "keywordMessages", values => do
        emitValue (.clauses (← flattenSurfaceClauses values))
    | "nonEmptyMessages", values => do
        emitValue (.clauses (← flattenSurfaceClauses values))
    | "messageCascade", [.clauses initial, .clauses subsequent] =>
        emitValue (.cascadeParts initial subsequent)
    | "cascadedExpression", [.expression expression] =>
        emitValue (.expression expression)
    | "cascadedExpression",
        [.expression receiver, .cascadeParts initial subsequent] =>
        emitValue (.expression (makeSurfaceCascade span receiver initial subsequent))
    | "expression", [.name setterName, .expression expression] =>
        emitValue (.expression (.setter span setterName expression))
    | "expression", [.expression expression] => emitValue (.expression expression)
    | "parenthesized", [.expression expression] =>
        emitValue (.expression (.parenthesized span expression))
    | "tuple", values => do
        emitValue (.expression (.tuple span (← collectExpressions values)))
    | "blockParameters", values => do
        emitValue (.declarations (← flattenSurfaceDeclarations values))
    | "codeBody", [.statements statements] =>
        emitValue (.codeBody ⟨span, none, statements⟩)
    | "codeBody", [.slotGroup locals, .statements statements] =>
        emitValue (.codeBody ⟨span, some locals, statements⟩)
    | "block", [.codeBody body] =>
        emitValue (.expression (.closure span [] (body.locals.toList) body.statements))
    | "block", [.declarations parameters, .codeBody body] =>
        emitValue (.expression
          (.closure span parameters (body.locals.toList) body.statements))
    | "returnStatement", [.expression expression] =>
        emitValue (.statement (.returnStatement span expression))
    | "statements", values => do
        emitValue (.statements (← flattenSurfaceStatements values))
    | "wildcardPattern", [] => emitValue (.pattern (.wildcard span))
    | "literalPattern", [.expression expression] =>
        emitValue (.pattern (.literal span expression))
    | "variablePattern", [.name variableName] =>
        emitValue (.pattern (.variable span variableName))
    | "nestedPattern", [.pattern pattern] =>
        emitValue (.pattern (.nested span pattern))
    | "keywordPatternPair", [.keyword keyword] =>
        emitValue (.patternPair keyword none)
    | "keywordPatternPair", [.keyword keyword, .pattern pattern] =>
        emitValue (.patternPair keyword (some pattern))
    | "keywordPattern", values => do
        emitValue (.pattern (.keyword span (← collectPatternPairs values)))
    | "pattern", [.pattern pattern] =>
        emitValue (.expression (.pattern span pattern))
    | "accessModifier", _ => do emitValue (.access (← decoders.access slice))
    | "keywordPatternDecl", values => do
        let pairs ← collectKeywordFormals values
        let spelling := pairs.foldl (fun current pair => current ++ pair.1) ""
        emitValue (.patternDeclaration
          ⟨span, ⟨spelling⟩, pairs.map Prod.snd⟩)
    | "binaryPatternDecl", [.selector selector, .declaration formal] =>
        emitValue (.patternDeclaration ⟨span, selector, [formal]⟩)
    | "messagePattern", [.selector selector] =>
        emitValue (.patternDeclaration ⟨span, selector, []⟩)
    | "messagePattern", [.patternDeclaration declaration] =>
        emitValue (.patternDeclaration declaration)
    | "slotDecl", [.name slotName] =>
        emitValue (.declaration (.formal span slotName))
    | "slotDef", [.declaration (.formal _ slotName)] =>
        emitValue (.declaration
          (.slot span none slotName (decoders.mutability slice) none))
    | "slotDef", [.declaration (.formal _ slotName), .expression initializer] =>
        emitValue (.declaration
          (.slot span none slotName (decoders.mutability slice) (some initializer)))
    | "slotDef", [.access access, .declaration (.formal _ slotName)] =>
        emitValue (.declaration
          (.slot span (some access) slotName (decoders.mutability slice) none))
    | "slotDef", [.access access, .declaration (.formal _ slotName),
        .expression initializer] =>
        emitValue (.declaration
          (.slot span (some access) slotName (decoders.mutability slice)
            (some initializer)))
    | "sequentialSlots", values => do
        emitValue (.slotGroup (.sequential span
          (← flattenSurfaceDeclarations values)))
    | "simultaneousSlots", values => do
        emitValue (.slotGroup (.simultaneous span
          (← flattenSurfaceDeclarations values)))
    | "lazySlotDecl", [.declaration (.formal _ slotName),
        .expression initializer] =>
        emitValue (.declaration
          (.lazySlot span none slotName (decoders.mutability slice) initializer))
    | "lazySlotDecl", [.access access, .declaration (.formal _ slotName),
        .expression initializer] =>
        emitValue (.declaration
          (.lazySlot span (some access) slotName (decoders.mutability slice)
            initializer))
    | "methodDecl", [.patternDeclaration pattern, .codeBody body] =>
        emitValue (.declaration
          (.method span none pattern.selector pattern.formals
            body.locals.toList body.statements))
    | "methodDecl", [.access access, .patternDeclaration pattern,
        .codeBody body] =>
        emitValue (.declaration
          (.method span (some access) pattern.selector pattern.formals
            body.locals.toList body.statements))
    | "nestedClassDecl", [.declaration declaration] =>
        emitValue (.declaration (.nestedClass span none declaration))
    | "nestedClassDecl", [.access access, .declaration declaration] =>
        emitValue (.declaration (.nestedClass span (some access) declaration))
    | "classHeader", [.statements statements] =>
        emitValue (.classHeader ⟨span, none, statements⟩)
    | "classHeader", [.slotGroup locals, .statements statements] =>
        emitValue (.classHeader ⟨span, some locals, statements⟩)
    | "instanceSide", values => do
        emitValue (.declarations (← flattenSurfaceDeclarations values))
    | "classSide", values => do
        emitValue (.declarations (← flattenSurfaceDeclarations values))
    | "classBody", [.classHeader header, .declarations instanceDeclarations] =>
        emitValue (.classStructure
          (.structure span header.locals header.statements instanceDeclarations []))
    | "classBody", [.classHeader header, .declarations instanceDeclarations,
        .declarations classDeclarations] =>
        emitValue (.classStructure
          (.structure span header.locals header.statements instanceDeclarations
            classDeclarations))
    | "inheritanceClause", [.selector selector] =>
        emitValue (.inheritanceHead
          (.head span (.implicitSend span selector [])
            (defaultInitializerClause span)))
    | "inheritanceClause", [.selector selector, .clause initializer] =>
        emitValue (.inheritanceHead
          (.head span (.implicitSend span selector []) initializer))
    | "inheritanceClause", [.expression receiver, .selector selector] =>
        emitValue (.inheritanceHead
          (.head span (.messageSend span receiver selector [])
            (defaultInitializerClause span)))
    | "inheritanceClause", [.expression receiver, .selector selector,
        .clause initializer] =>
        emitValue (.inheritanceHead
          (.head span (.messageSend span receiver selector []) initializer))
    | "mixinSuffix", values => do
        let result ← collectMixinTail values
        emitValue (.mixinTail ⟨span, result.1, result.2⟩)
    | "inheritanceAndBody", [.classStructure classStructure] =>
        emitValue (.inheritance (.defaultInheritance span classStructure))
    | "inheritanceAndBody", [.inheritanceHead head,
        .classStructure classStructure] =>
        emitValue (.inheritance
          (.explicitInheritance span head.receiver head.initializer classStructure))
    | "inheritanceAndBody", [.inheritanceHead head, .mixinTail tail] =>
        emitValue (.inheritance
          (.mixinChain span head.receiver head.initializer tail.heads
            tail.classStructure))
    | "classDeclaration", [.name className, .inheritance inheritance] =>
        emitValue (.declaration
          (.classDeclaration span className ⟨"new"⟩ [] inheritance))
    | "classDeclaration", [.name className,
        .patternDeclaration factory, .inheritance inheritance] =>
        emitValue (.declaration
          (.classDeclaration span className factory.selector factory.formals inheritance))
    | "objectLiteral", [.classStructure classStructure] =>
        emitValue (.expression
          (.objectLiteral span (.implicitHeader span classStructure)))
    | "objectLiteral", [.name receiverName, .classStructure classStructure] =>
        emitValue (.expression
          (.objectLiteral span
            (.explicitHeader span (.identifier span receiverName)
              (defaultInitializerClause span) classStructure)))
    | "objectLiteral", [.name receiverName, .clause initializer,
        .classStructure classStructure] =>
        emitValue (.expression
          (.objectLiteral span
            (.explicitHeader span (.identifier span receiverName)
              initializer classStructure)))
    | "compilationUnit", [.name language, .declaration declaration] =>
        emitValue (.compilationUnit ⟨span, language, none, declaration⟩)
    | "compilationUnit", [.name language,
        .expression (.atom _ (.string category)), .declaration declaration] =>
        emitValue (.compilationUnit ⟨span, language, some category, declaration⟩)
    | _, _ => none
where
  collectExpressions : List SurfaceActionValue → Option (List SurfaceExpression)
    | [] => some []
    | .expression expression :: remaining => do
        pure (expression :: (← collectExpressions remaining))
    | _ => none
  collectKeywordArguments : List SurfaceActionValue →
      Option (List (String × SurfaceExpression))
    | [] => some []
    | .keyword keyword :: .expression argument :: remaining => do
        pure ((keyword, argument) :: (← collectKeywordArguments remaining))
    | _ => none
  collectPatternPairs : List SurfaceActionValue →
      Option (List (Selector × Option SurfacePattern))
    | [] => some []
    | .patternPair keyword pattern :: remaining => do
        pure ((⟨keyword⟩, pattern) :: (← collectPatternPairs remaining))
    | _ => none
  collectKeywordFormals : List SurfaceActionValue →
      Option (List (String × SurfaceDeclaration))
    | [] => some []
    | .keyword keyword :: .declaration formal :: remaining => do
        pure ((keyword, formal) :: (← collectKeywordFormals remaining))
    | _ => none
  defaultInitializerClause (clauseSpan : SourceSpan) : SurfaceClause :=
    .clause clauseSpan ⟨"new"⟩ []
  collectMixinTail : List SurfaceActionValue →
      Option (List SurfaceInheritanceHead × Option SurfaceClassStructure)
    | [] => some ([], none)
    | [.classStructure classStructure] => some ([], some classStructure)
    | .inheritanceHead head :: remaining => do
        let tail ← collectMixinTail remaining
        pure (head :: tail.1, tail.2)
    | _ => none

def newspeakSurfaceSemantics (decoders : NewspeakLexicalDecoders) :
    PEGActionSemantics SurfaceActionValue SurfaceMetadata :=
  { token := surfaceActionToken
    action := newspeakSurfaceAction decoders }

def PEGParsesNewspeakUnit (grammar : PEGGrammar)
    (decoders : NewspeakLexicalDecoders) (source : SourceText)
    (unit : SurfaceCompilationUnit) (metadata : List SurfaceMetadata) : Prop :=
  PEGGrammarWellFormed grammar ∧
    PEGParsesAST grammar (newspeakSurfaceSemantics decoders) source
      (.compilationUnit unit) metadata

theorem PEGParsesNewspeakUnit.deterministic
    {grammar : PEGGrammar} {decoders : NewspeakLexicalDecoders}
    {source : SourceText} {first second : SurfaceCompilationUnit}
    {firstMetadata secondMetadata : List SurfaceMetadata}
    (firstParse : PEGParsesNewspeakUnit grammar decoders source first firstMetadata)
    (secondParse : PEGParsesNewspeakUnit grammar decoders source second secondMetadata) :
    first = second ∧ firstMetadata = secondMetadata := by
  have result := PEGParsesAST.deterministic firstParse.2 secondParse.2
  exact ⟨SurfaceActionValue.compilationUnit.inj result.1, result.2⟩

end Newspeak
