import Newspeak.PEG

namespace Newspeak

def PEGNullable (grammar : PEGGrammar) (expression : PEGExpr) : Prop :=
  ∃ forest, PEGRecognizes grammar [] expression 0 (.success 0 forest)

inductive PEGReferencesNonterminal : PEGExpr → Nonterminal → Prop where
  | nonterminal (name) : PEGReferencesNonterminal (.nonterminal name) name
  | sequenceLeft {first second name} :
      PEGReferencesNonterminal first name →
      PEGReferencesNonterminal (.sequence first second) name
  | sequenceRight {first second name} :
      PEGReferencesNonterminal second name →
      PEGReferencesNonterminal (.sequence first second) name
  | choiceLeft {first second name} :
      PEGReferencesNonterminal first name →
      PEGReferencesNonterminal (.orderedChoice first second) name
  | choiceRight {first second name} :
      PEGReferencesNonterminal second name →
      PEGReferencesNonterminal (.orderedChoice first second) name
  | star {body name} : PEGReferencesNonterminal body name →
      PEGReferencesNonterminal (.star body) name
  | notAhead {body name} : PEGReferencesNonterminal body name →
      PEGReferencesNonterminal (.notAhead body) name
  | andAhead {body name} : PEGReferencesNonterminal body name →
      PEGReferencesNonterminal (.andAhead body) name
  | capture {captureName body name} : PEGReferencesNonterminal body name →
      PEGReferencesNonterminal (.capture captureName body) name

inductive PEGSubexpression : PEGExpr → PEGExpr → Prop where
  | here (expression) : PEGSubexpression expression expression
  | sequenceLeft {subexpression first second} :
      PEGSubexpression subexpression first →
      PEGSubexpression subexpression (.sequence first second)
  | sequenceRight {subexpression first second} :
      PEGSubexpression subexpression second →
      PEGSubexpression subexpression (.sequence first second)
  | choiceLeft {subexpression first second} :
      PEGSubexpression subexpression first →
      PEGSubexpression subexpression (.orderedChoice first second)
  | choiceRight {subexpression first second} :
      PEGSubexpression subexpression second →
      PEGSubexpression subexpression (.orderedChoice first second)
  | star {subexpression body} : PEGSubexpression subexpression body →
      PEGSubexpression subexpression (.star body)
  | notAhead {subexpression body} : PEGSubexpression subexpression body →
      PEGSubexpression subexpression (.notAhead body)
  | andAhead {subexpression body} : PEGSubexpression subexpression body →
      PEGSubexpression subexpression (.andAhead body)
  | capture {subexpression name body} : PEGSubexpression subexpression body →
      PEGSubexpression subexpression (.capture name body)

/-- A nonterminal can be invoked from an expression before any character is
    consumed.  The second half of a sequence is leading only when the first
    half can succeed without consumption. -/
inductive PEGLeadingNonterminal (grammar : PEGGrammar) :
    PEGExpr → Nonterminal → Prop where
  | nonterminal (name) : PEGLeadingNonterminal grammar (.nonterminal name) name
  | sequenceLeft {first second name} :
      PEGLeadingNonterminal grammar first name →
      PEGLeadingNonterminal grammar (.sequence first second) name
  | sequenceRight {first second name} :
      PEGNullable grammar first →
      PEGLeadingNonterminal grammar second name →
      PEGLeadingNonterminal grammar (.sequence first second) name
  | choiceLeft {first second name} :
      PEGLeadingNonterminal grammar first name →
      PEGLeadingNonterminal grammar (.orderedChoice first second) name
  | choiceRight {first second name} :
      PEGLeadingNonterminal grammar second name →
      PEGLeadingNonterminal grammar (.orderedChoice first second) name
  | star {body name} : PEGLeadingNonterminal grammar body name →
      PEGLeadingNonterminal grammar (.star body) name
  | notAhead {body name} : PEGLeadingNonterminal grammar body name →
      PEGLeadingNonterminal grammar (.notAhead body) name
  | andAhead {body name} : PEGLeadingNonterminal grammar body name →
      PEGLeadingNonterminal grammar (.andAhead body) name
  | capture {captureName body name} :
      PEGLeadingNonterminal grammar body name →
      PEGLeadingNonterminal grammar (.capture captureName body) name

def PEGLeads (grammar : PEGGrammar) (source target : Nonterminal) : Prop :=
  ∃ body, grammar.rules source = some body ∧
    PEGLeadingNonterminal grammar body target

inductive PEGLeadsPlus (grammar : PEGGrammar) :
    Nonterminal → Nonterminal → Prop where
  | single {source target} : PEGLeads grammar source target →
      PEGLeadsPlus grammar source target
  | step {source middle target} : PEGLeads grammar source middle →
      PEGLeadsPlus grammar middle target →
      PEGLeadsPlus grammar source target

structure PEGGrammarWellFormed (grammar : PEGGrammar) : Prop where
  startDefined : grammar.rules grammar.start ≠ none
  referencesDefined :
    ∀ {source body target}, grammar.rules source = some body →
      PEGReferencesNonterminal body target → grammar.rules target ≠ none
  noLeftRecursion : ∀ name, ¬PEGLeadsPlus grammar name name
  repetitionAdvances :
    ∀ {source body repeated}, grammar.rules source = some body →
      PEGSubexpression (.star repeated) body → ¬PEGNullable grammar repeated

def AdmissiblePEGCompleteParse (grammar : PEGGrammar) (source : SourceText)
    (tree : ConcreteTree) : Prop :=
  PEGGrammarWellFormed grammar ∧ PEGCompleteParse grammar source tree

theorem AdmissiblePEGCompleteParse.unique
    {grammar : PEGGrammar} {source : SourceText}
    {firstTree secondTree : ConcreteTree}
    (first : AdmissiblePEGCompleteParse grammar source firstTree)
    (second : AdmissiblePEGCompleteParse grammar source secondTree) :
    firstTree = secondTree :=
  PEGCompleteParse.unique first.2 second.2

end Newspeak
