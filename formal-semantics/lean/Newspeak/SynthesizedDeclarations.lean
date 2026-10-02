import Newspeak.Program
import Newspeak.SourceIdentification
import Newspeak.SurfaceSyntax

namespace Newspeak

def declarationMethodIdentity (declaration : DeclId) : MethodId :=
  ⟨2 * declaration.index⟩

def declarationActivationIdentity (declaration : DeclId) : ActivationDeclId :=
  ⟨2 * declaration.index⟩

def declarationParameterIdentity (declaration : DeclId) : ParameterId :=
  ⟨declaration.index⟩

def declarationLocalIdentity (declaration : DeclId) : LocalSlotId :=
  ⟨declaration.index⟩

def declarationSlotIdentity (declaration : DeclId) : SlotId :=
  ⟨declaration.index⟩

def cantorPairNat (left right : Nat) : Nat :=
  let diagonal := left + right
  (diagonal * (diagonal + 1)) / 2 + right

def synthesizedMethodIdentity (declaration : DeclId) (tag : Nat) : MethodId :=
  ⟨2 * cantorPairNat declaration.index tag + 1⟩

def synthesizedActivationIdentity (declaration : DeclId) (tag : Nat) :
    ActivationDeclId :=
  ⟨2 * cantorPairNat declaration.index tag + 1⟩

def synthesizedParameterIdentity (declaration : DeclId) (tag : Nat) :
    ParameterId :=
  ⟨cantorPairNat declaration.index tag⟩

def accessOrProtected : Option Access → Access
  | none => .protectedAccess
  | some access => access

def setterSelector (name : String) : Selector := ⟨name ++ ":"⟩

def declarationImmediateClass : ClassBodyDecl → Option ClassDeclId
  | .namedClass declaration => some declaration
  | .objectLiteral _ => none

structure DerivedMethod where
  definition : MethodDef
  locals : List LocalDeclarationGroup
  body : List Statement

def synthesizedGetter (declaration : DeclId) (owner : ClassBodyDecl)
    (name : String) (access : Access) (value : CoreExpr) : DerivedMethod :=
  let method := synthesizedMethodIdentity declaration 0
  let activation := synthesizedActivationIdentity declaration 0
  { definition :=
      { identity := method
        activationDeclaration := activation
        selector := ⟨name⟩
        access := access
        parameters := []
        locals := []
        owner := owner
        body := ⟨declaration.index⟩ }
    locals := []
    body := [.return value] }

def synthesizedSetter (declaration : DeclId) (owner : ClassBodyDecl)
    (name : String) (access : Access) (slot : SlotId) : DerivedMethod :=
  let method := synthesizedMethodIdentity declaration 1
  let activation := synthesizedActivationIdentity declaration 1
  let parameter := synthesizedParameterIdentity declaration 1
  let parameterName : Selector := ⟨"$value"⟩
  let parameterRead : CoreExpr :=
    .implicitSend parameterName [] (some (.activationDecl activation))
      (declarationImmediateClass owner)
  { definition :=
      { identity := method
        activationDeclaration := activation
        selector := setterSelector name
        access := access
        parameters := [parameter]
        locals := []
        owner := owner
        body := ⟨declaration.index⟩ }
    locals := []
    body := [.expression (.currentWrite slot parameterRead),
      .expression parameterRead] }

def ordinarySlotMethods (declaration : DeclId) (owner : ClassBodyDecl)
    (name : String) (access : Access) (mutability : SurfaceMutability) :
    List DerivedMethod :=
  let slot := declarationSlotIdentity declaration
  let getter := synthesizedGetter declaration owner name access (.currentRead slot)
  match mutability with
  | .immutable => [getter]
  | .mutable => [getter, synthesizedSetter declaration owner name access slot]

def lazySlotMethods (declaration : DeclId) (owner : ClassBodyDecl)
    (name : String) (access : Access) (mutability : SurfaceMutability)
    (initializer : CoreExpr) : List DerivedMethod :=
  let slot := declarationSlotIdentity declaration
  let getter := synthesizedGetter declaration owner name access
    (.lazyRead slot initializer)
  match mutability with
  | .immutable => [getter]
  | .mutable => [getter, synthesizedSetter declaration owner name access slot]

def primaryFactoryMethod (declaration : DeclId) (owner : ClassBodyDecl)
    (selector : Selector) (parameters : List ParameterId) : DerivedMethod :=
  { definition :=
      { identity := synthesizedMethodIdentity declaration 20
        activationDeclaration := synthesizedActivationIdentity declaration 20
        selector := selector
        access := .publicAccess
        parameters := parameters
        locals := []
        owner := owner
        body := ⟨declaration.index⟩ }
    locals := []
    body := [.return (.newInstanceCurrent selector parameters)] }

theorem ordinarySlotMethods_mutable_setter_same_access
    (declaration : DeclId) (owner : ClassBodyDecl) (name : String)
    (access : Access) :
    ((ordinarySlotMethods declaration owner name access .mutable)[1]?).map
      (fun method => method.definition.access) = some access := by
  simp [ordinarySlotMethods, synthesizedSetter, synthesizedGetter]

theorem lazySlotMethods_mutable_setter_same_access
    (declaration : DeclId) (owner : ClassBodyDecl) (name : String)
    (access : Access) (initializer : CoreExpr) :
    ((lazySlotMethods declaration owner name access .mutable initializer)[1]?).map
      (fun method => method.definition.access) = some access := by
  simp [lazySlotMethods, synthesizedSetter, synthesizedGetter]

end Newspeak
