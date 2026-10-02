import Newspeak.PEG

namespace Newspeak

namespace PEGExpr

def sequences : List PEGExpr → PEGExpr
  | [] => .empty
  | [expression] => expression
  | expression :: remaining => .sequence expression (sequences remaining)

def choices : PEGExpr → List PEGExpr → PEGExpr
  | expression, [] => expression
  | expression, alternative :: remaining =>
      .orderedChoice expression (choices alternative remaining)

def optional (expression : PEGExpr) : PEGExpr :=
  .orderedChoice expression .empty

def plus (expression : PEGExpr) : PEGExpr :=
  .sequence expression (.star expression)

def literal (text : String) : PEGExpr :=
  sequences (text.toList.map .character)

def nt (name : Nonterminal) : PEGExpr := .nonterminal name

end PEGExpr

structure NewspeakCharacterClasses where
  whiteSpace : Char → Bool
  asciiLetter : Char → Bool
  asciiUpper : Char → Bool
  decimalDigit : Char → Bool
  specialCharacter : Char → Bool

def finiteStoreFromEntries {Key Value : Type} [DecidableEq Key]
    (entries : List (Key × Value)) : FiniteStore Key Value :=
  entries.foldl (fun store entry => store.install entry.1 entry.2)
    (FiniteStore.empty Key Value)

def newspeakRule (name : Nonterminal) (body : PEGExpr) :
    Nonterminal × PEGExpr :=
  (name, .capture name body)

def punctuationName (punctuation : String) : Nonterminal :=
  "T_" ++ punctuation

def newspeakTrivia : PEGExpr :=
  .star (.orderedChoice (.nonterminal "white") (.nonterminal "comment"))

def newspeakToken (text : String) : PEGExpr :=
  .sequence newspeakTrivia (.literal text)

def newspeakWord (text : String) : PEGExpr :=
  .sequences [newspeakTrivia, .literal text, .notAhead (.nt "idRest")]

def punctuationRule (punctuation : String) : Nonterminal × PEGExpr :=
  newspeakRule (punctuationName punctuation) (newspeakToken punctuation)

def newspeakPunctuation : List String :=
  [":", ",", ".", "||", "=", "^", "[", "{", "(", "<", "<:",
   "#", ">", "]", "}", ")", ";", "/", "|", "::=", "<-:"]

def t (punctuation : String) : PEGExpr :=
  .nt (punctuationName punctuation)

def newspeakTypeWords : List String :=
  ["arg", "for", "generic", "inheritedTypeOf", "is", "message", "of",
   "receiverType", "subtypeOf", "typeArg", "where"]

def typeWordName (word : String) : Nonterminal := "TW_" ++ word

def typeWord (word : String) : PEGExpr := .nt (typeWordName word)

def typeWordRule (word : String) : Nonterminal × PEGExpr :=
  newspeakRule (typeWordName word) (newspeakWord word)

def newspeakGrammarEntries (classes : NewspeakCharacterClasses) :
    List (Nonterminal × PEGExpr) :=
  newspeakPunctuation.map punctuationRule ++
  [ newspeakRule "white" (.characterSet classes.whiteSpace)
  , newspeakRule "idRest"
      (.orderedChoice
        (.characterSet fun character =>
          classes.asciiLetter character || classes.decimalDigit character)
        (.character '_'))
  , newspeakRule "rawId"
      (.sequence
        (.orderedChoice (.characterSet classes.asciiLetter) (.character '_'))
        (.star (.nt "idRest")))
  , newspeakRule "id"
      (.sequences [newspeakTrivia, .notAhead (.nt "reservedWord"), .nt "rawId"])
  , newspeakRule "rawKeyword" (.sequence (.nt "rawId") (.character ':'))
  , newspeakRule "keyword" (.sequence newspeakTrivia (.nt "rawKeyword"))
  , newspeakRule "setterKeyword"
      (.sequences [newspeakTrivia, .nt "rawKeyword", .character ':'])
  , newspeakRule "keywords" (.plus (.nt "rawKeyword"))
  , newspeakRule "rawBinary"
      (.sequence
        (.orderedChoice (.characterSet classes.specialCharacter)
          (.character '-'))
        (.star (.characterSet classes.specialCharacter)))
  , newspeakRule "binarySelector"
      (.sequence newspeakTrivia (.nt "rawBinary"))
  , newspeakRule "metadataTag"
      (.sequences [.character ':', .nt "rawId", .character ':'])
  , newspeakRule "commentItem"
      (.orderedChoice
        (.sequence (.notAhead (.literal "*)")) .any)
        (.nt "comment"))
  , newspeakRule "comment"
      (.sequences [.literal "(*", .optional (.nt "metadataTag"),
        .star (.nt "commentItem"), .literal "*)"])
  , newspeakRule "reservedWord"
      (.choices (newspeakWord "self")
        [newspeakWord "super", newspeakWord "outer", newspeakWord "true",
         newspeakWord "false", newspeakWord "nil"])
  , newspeakRule "selfToken" (newspeakWord "self")
  , newspeakRule "superToken" (newspeakWord "super")
  , newspeakRule "outerToken" (newspeakWord "outer")
  , newspeakRule "trueToken" (newspeakWord "true")
  , newspeakRule "falseToken" (newspeakWord "false")
  , newspeakRule "nilToken" (newspeakWord "nil")
  , newspeakRule "classToken" (newspeakWord "class")
  , newspeakRule "lazyModifier" (newspeakWord "lazy")
  , newspeakRule "digits" (.plus (.characterSet classes.decimalDigit))
  , newspeakRule "extendedDigits"
      (.plus (.characterSet fun character =>
        classes.decimalDigit character || classes.asciiUpper character))
  , newspeakRule "fraction" (.sequence (t ".") (.nt "digits"))
  , newspeakRule "extendedFraction"
      (.sequence (t ".") (.nt "extendedDigits"))
  , newspeakRule "exponent"
      (.sequences [.character 'e', .optional (.character '-'), .nt "digits"])
  , newspeakRule "decimalNum"
      (.sequences [.optional (.character '-'), .nt "digits",
        .optional (.nt "fraction"), .optional (.nt "exponent")])
  , newspeakRule "radixNum"
      (.sequences [.nt "digits", .character 'r', .optional (.character '-'),
        .nt "extendedDigits", .optional (.nt "extendedFraction"),
        .optional (.nt "exponent")])
  , newspeakRule "number"
      (.sequence newspeakTrivia
        (.orderedChoice (.nt "radixNum") (.nt "decimalNum")))
  , newspeakRule "singleString"
      (.sequences [.character '\'',
        .star (.orderedChoice (.literal "''")
          (.sequence (.notAhead (.character '\'')) .any)),
        .character '\''])
  , newspeakRule "doubleString"
      (.sequences [.character '"',
        .star (.orderedChoice (.literal "\"\"")
          (.sequence (.notAhead (.character '"')) .any)),
        .character '"'])
  , newspeakRule "string"
      (.sequence newspeakTrivia
        (.orderedChoice (.nt "singleString") (.nt "doubleString")))
  , newspeakRule "symbol"
      (.sequences [newspeakTrivia, t "#",
        .choices (.nt "string")
          [.nt "keywords", .nt "rawBinary", .nt "rawId"]])
  , newspeakRule "unarySelector" (.nt "id")
  , newspeakRule "binaryMessage"
      (.sequence (.nt "binarySelector") (.nt "unaryExpression"))
  , newspeakRule "keywordMessage"
      (.plus (.sequence (.nt "keyword") (.nt "binaryExpression")))
  , newspeakRule "message"
      (.choices (.nt "keywordMessage") [.nt "binaryMessage", .nt "unarySelector"])
  , newspeakRule "outerReceiver" (.sequence (.nt "outerToken") (.nt "id"))
  , newspeakRule "receiverPrimary"
      (.choices (.nt "outerReceiver") [.nt "superToken", .nt "primary"])
  , newspeakRule "unaryExpression"
      (.sequence (.nt "receiverPrimary") (.star (.nt "unarySelector")))
  , newspeakRule "binaryExpression"
      (.sequence (.nt "unaryExpression") (.star (.nt "binaryMessage")))
  , newspeakRule "keywordExpression"
      (.sequence (.nt "binaryExpression") (.optional (.nt "keywordMessage")))
  , newspeakRule "eventualExpression"
      (.sequences [.nt "keywordExpression", t "<-:", .nt "message"])
  , newspeakRule "cascadeMessage"
      (.sequence (t ";")
        (.choices (.nt "keywordMessage") [.nt "binaryMessage", .nt "unarySelector"]))
  , newspeakRule "implicitKeywordSend" (.nt "keywordMessage")
  , newspeakRule "nontrivialUnaryMessages"
      (.sequences [.plus (.nt "unarySelector"), .star (.nt "binaryMessage"),
        .optional (.nt "keywordMessage")])
  , newspeakRule "nontrivialBinaryMessages"
      (.sequence (.plus (.nt "binaryMessage")) (.optional (.nt "keywordMessage")))
  , newspeakRule "keywordMessages" (.nt "keywordMessage")
  , newspeakRule "nonEmptyMessages"
      (.choices (.nt "nontrivialUnaryMessages")
        [.nt "nontrivialBinaryMessages", .nt "keywordMessages"])
  , newspeakRule "messageCascade"
      (.sequence (.nt "nonEmptyMessages") (.star (.nt "cascadeMessage")))
  , newspeakRule "cascadedExpression"
      (.sequence (.nt "primary") (.optional (.nt "messageCascade")))
  , newspeakRule "sendExpression"
      (.choices (.nt "eventualExpression")
        [.nt "implicitKeywordSend", .nt "cascadedExpression"])
  , newspeakRule "expression"
      (.sequence (.optional (.nt "setterKeyword")) (.nt "sendExpression"))
  , newspeakRule "literal"
      (.choices (.nt "pattern") [.nt "number", .nt "symbol", .nt "string",
        .nt "tuple", .nt "trueToken", .nt "falseToken", .nt "nilToken"])
  , newspeakRule "tuple"
      (.sequences [t "{",
        .optional (.sequences [.nt "expression",
          .star (.sequence (t ".") (.nt "expression")), .optional (t ".")]),
        t "}"])
  , newspeakRule "blockParameter" (.sequence (t ":") (.nt "slotDecl"))
  , newspeakRule "blockParameters"
      (.sequence (.plus (.nt "blockParameter")) (t "|"))
  , newspeakRule "block"
      (.sequences [t "[", .optional (.nt "blockParameters"), .nt "codeBody", t "]"])
  , newspeakRule "pattern"
      (.sequences [t "<", .nt "patternLiteral", t ">"])
  , newspeakRule "patternLiteral"
      (.choices (.nt "wildcardPattern") [.nt "literalPattern", .nt "keywordPattern"])
  , newspeakRule "wildcardPattern" (newspeakToken "_")
  , newspeakRule "literalPattern"
      (.choices (.nt "number") [.nt "symbol", .nt "string", .nt "tuple"])
  , newspeakRule "keywordPattern" (.plus (.nt "keywordPatternPair"))
  , newspeakRule "keywordPatternPair"
      (.sequence (.nt "keyword") (.optional (.nt "keywordPatternValue")))
  , newspeakRule "keywordPatternValue"
      (.choices (.nt "wildcardPattern")
        [.nt "literalPattern", .nt "variablePattern", .nt "nestedPattern"])
  , newspeakRule "variablePattern"
      (.sequences [newspeakTrivia, .character '?', .nt "rawId"])
  , newspeakRule "nestedPattern" (.sequence newspeakTrivia (.nt "pattern"))
  , newspeakRule "parenthesized"
      (.sequences [t "(", .nt "expression", t ")"])
  , newspeakRule "primary"
      (.choices (.nt "literal") [.nt "block", .nt "classDeclaration",
        .nt "objectLiteral", .nt "parenthesized", .nt "selfToken",
        .nt "unarySelector"])
  , newspeakRule "returnStatement"
      (.sequences [t "^", .nt "expression", .optional (t ".")])
  , newspeakRule "statements"
      (.choices (.nt "returnStatement")
        [.sequence (.nt "expression")
          (.optional (.sequence (t ".") (.nt "statements"))), .empty])
  , newspeakRule "codeBody"
      (.sequence (.optional (.nt "slotDecls")) (.nt "statements"))
  , newspeakRule "messagePattern"
      (.sequence
        (.choices (.nt "keywordPatternDecl")
          [.nt "binaryPatternDecl", .nt "unarySelector"])
        (.optional (.nt "returnType")))
  , newspeakRule "keywordPatternDecl"
      (.plus (.sequence (.nt "keyword") (.nt "slotDecl")))
  , newspeakRule "binaryPatternDecl"
      (.sequence (.nt "binarySelector") (.nt "slotDecl"))
  , newspeakRule "accessModifier"
      (.choices (newspeakToken "private")
        [newspeakToken "public", newspeakToken "protected"])
  , newspeakRule "methodDecl"
      (.sequences [.optional (.nt "accessModifier"), .nt "messagePattern",
        t "=", t "(", .nt "codeBody", t ")"])
  , newspeakRule "slotDecl" (.sequence (.nt "id") (.optional (.nt "type")))
  , newspeakRule "slotDef"
      (.sequences [.optional (.nt "accessModifier"), .nt "slotDecl",
        .optional (.orderedChoice
          (.sequences [.orderedChoice (t "=") (t "::="),
            .nt "expression", t "."])
          (t "."))])
  , newspeakRule "sequentialSlots"
      (.sequences [t "|", .star (.nt "slotDef"), t "|"])
  , newspeakRule "simultaneousSlots"
      (.sequences [t "||", .star (.nt "slotDef"), t "||"])
  , newspeakRule "slotDecls"
      (.orderedChoice (.nt "sequentialSlots") (.nt "simultaneousSlots"))
  , newspeakRule "lazySlotDecl"
      (.sequences [.orderedChoice
          (.sequence (.nt "lazyModifier") (.optional (.nt "accessModifier")))
          (.sequence (.nt "accessModifier") (.nt "lazyModifier")),
        .nt "slotDecl", .orderedChoice (t "=") (t "::="),
        .nt "expression", t "."])
  , newspeakRule "classHeader"
      (.sequences [t "(", .optional (.nt "comment"),
        .optional (.nt "slotDecls"), .nt "statements", t ")"])
  , newspeakRule "nestedClassDecl"
      (.sequence (.optional (.nt "accessModifier")) (.nt "classDeclaration"))
  , newspeakRule "instanceSide"
      (.sequences [t "(", .star (.choices (.nt "nestedClassDecl")
        [.nt "lazySlotDecl", .nt "methodDecl"]), t ")"])
  , newspeakRule "classSide"
      (.sequences [t ":", t "(", .star (.nt "methodDecl"), t ")"])
  , newspeakRule "classBody"
      (.sequences [.nt "classHeader", .nt "instanceSide",
        .optional (.nt "classSide")])
  , newspeakRule "inheritancePrefix"
      (.choices (.nt "outerReceiver") [.nt "selfToken", .nt "superToken"])
  , newspeakRule "inheritanceClause"
      (.sequences [.optional (.nt "inheritancePrefix"), .nt "unarySelector",
        .optional (.nt "message")])
  , newspeakRule "mixinSuffix"
      (.sequences [.plus (.sequence (t "<:") (.nt "inheritanceClause")),
        .orderedChoice (t ".") (.nt "classBody")])
  , newspeakRule "inheritanceAndBody"
      (.orderedChoice (.nt "classBody")
        (.sequence (.nt "inheritanceClause")
          (.orderedChoice (.nt "classBody") (.nt "mixinSuffix"))))
  , newspeakRule "classDeclaration"
      (.sequences [.nt "classToken", .nt "id",
        .optional (.nt "typeParameterDecl"), .optional (.nt "messagePattern"),
        t "=", .nt "inheritanceAndBody"])
  , newspeakRule "objectLiteral"
      (.sequence
        (.optional (.sequence (.nt "id") (.optional (.nt "keywordMessage"))))
        (.nt "classBody"))
  , newspeakRule "compilationUnit"
      (.sequences [.nt "id", .optional (.nt "string"),
        .nt "classDeclaration", newspeakTrivia])
  ] ++ newspeakTypeGrammarEntries ++ newspeakTypeWords.map typeWordRule
where
  newspeakTypeGrammarEntries : List (Nonterminal × PEGExpr) :=
    [ newspeakRule "returnType" (.sequence (t "^") (.nt "type"))
    , newspeakRule "type" (.sequences [t "<", .nt "typeExpr", t ">"])
    , newspeakRule "typePrimary"
        (.sequence (.nt "id") (.optional (.nt "typeArguments")))
    , newspeakRule "typeFactor"
        (.choices (.nt "typePrimary") [.nt "blockType", .nt "tupleType",
          .nt "parenthesizedTypeExpression"])
    , newspeakRule "parenthesizedTypeExpression"
        (.sequences [t "(", .nt "typeExpr", t ")"])
    , newspeakRule "typeTerm"
        (.sequence (.nt "typeFactor") (.star (.nt "id")))
    , newspeakRule "typeExpr"
        (.sequence (.nt "typeTerm")
          (.optional (.sequence (.choices (t "|") [t ";", t "/"])
            (.nt "typeExpr"))))
    , newspeakRule "typeArguments"
        (.sequences [t "[", .nt "typeExpr",
          .star (.sequence (t ",") (.nt "typeExpr")), t "]"])
    , newspeakRule "tupleType"
        (.sequences [t "{", .optional (.sequence (.nt "typeExpr")
          (.star (.sequence (t ".") (.nt "typeExpr")))), t "}"])
    , newspeakRule "blockArgType" (.sequence (t ":") (.nt "typeTerm"))
    , newspeakRule "blockReturnType" (.nt "typeExpr")
    , newspeakRule "nonEmptyBlockArgList"
        (.sequence (.plus (.nt "blockArgType"))
          (.optional (.sequence (t "|") (.nt "blockReturnType"))))
    , newspeakRule "blockType"
        (.sequences [t "[", .orderedChoice (.nt "nonEmptyBlockArgList")
          (.optional (.nt "blockReturnType")), t "]"])
    , newspeakRule "typeParameterDecl"
        (.sequences [t "<", t "[", .nt "id",
          .star (.sequence (t ",") (.nt "id")), t "]", t ">"])
    , newspeakRule "typePattern"
        (.sequences [t "<", .nt "typeFormal",
          .star (.sequence (t ";") (.nt "typeFormal")), t ">"])
    , newspeakRule "typeFormal"
        (.sequences [typeWord "where", .nt "id",
          .optional (.nt "typeParamConstraint"), typeWord "is",
          .nt "inferenceClause"])
    , newspeakRule "typeParamConstraint"
        (.sequences [t "<", .optional (.nt "typeBoundQualifier"),
          .nt "typeExpr", t ">"])
    , newspeakRule "typeBoundQualifier"
        (.orderedChoice (typeWord "subtypeOf") (typeWord "inheritedTypeOf"))
    , newspeakRule "inferenceClause"
        (.choices (typeWord "receiverType")
          [.sequence (.nt "returnType") (.nt "returnTypeInferenceClause"),
           .nt "typeArgInferenceClause",
           .sequences [typeWord "arg", .nt "number",
             .optional (.sequence (typeWord "of") (.nt "msgSelector"))]])
    , newspeakRule "returnTypeInferenceClause"
        (.sequence (typeWord "of") (.nt "msgSelector"))
    , newspeakRule "msgSelector"
        (.sequences [.nt "symbol", typeWord "message", typeWord "of",
          .nt "inferenceClause"])
    , newspeakRule "typeArgInferenceClause"
        (.sequences [typeWord "typeArg", .nt "number", typeWord "for",
          typeWord "generic", .nt "symbol", typeWord "of",
          .nt "inferenceClause"])
    ]

def newspeakGrammar (classes : NewspeakCharacterClasses) : PEGGrammar :=
  { start := "compilationUnit"
    rules := finiteStoreFromEntries (newspeakGrammarEntries classes) }

@[simp] theorem newspeakGrammar_start (classes : NewspeakCharacterClasses) :
    (newspeakGrammar classes).start = "compilationUnit" := by
  rfl

end Newspeak
