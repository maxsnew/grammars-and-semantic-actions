import LambekD.Core.Base

/-!
# Linear type connectives for Lambek^D

All grammar connectives, notation, and eliminators.
No metaprogramming dependencies.
-/

namespace LambekD

universe uAlph

variable {Alphabet : Type uAlph}

structure Tensor
  (A B : Grammar Alphabet)
  (w : String Alphabet) where
  split : Splitting w
  fst : A split.left
  snd : B split.right

def Epsilon.{u} : Grammar.{u} Alphabet := fun w => ULift.{u} (PLift (w = []))
def Literal.{u} (c : Alphabet) : Grammar.{u} Alphabet := fun w => ULift.{u} (PLift (w = [c]))
def FunctionR (A B : Grammar Alphabet) : Grammar Alphabet := fun w => ∀ w', A w' → B (w' ++ w)
def FunctionL (B A : Grammar Alphabet)
  : Grammar Alphabet := fun w => ∀ w', A w' → B (w ++ w')
def Sum (A : Grammar Alphabet) (B : Grammar Alphabet)
  : Grammar Alphabet := fun w => A w ⊕ B w
def Product (A : Grammar Alphabet) (B : Grammar Alphabet)
  : Grammar Alphabet := fun w => A w × B w
def Top.{u} : Grammar.{u} Alphabet := fun _ => ULift.{u} PUnit
def Bottom.{u} : Grammar.{u} Alphabet := fun _ => ULift.{u} PEmpty
def IdxProduct.{v} (X : Type v) (F : X → Grammar Alphabet) : Grammar Alphabet := fun w => ∀ x, F x w
def IdxCoproduct.{v} (X : Type v) (F : X → Grammar Alphabet) : Grammar Alphabet := fun w => Σ x, F x w

def GrammarTerm (A B : Grammar Alphabet) := ∀ w, A w → B w

scoped infixr:70 " ⊗ "  => Tensor
scoped infixr:60 " ⊸ "  => FunctionR
scoped infixl:60 " ⟜ "  => FunctionL
scoped infixl:65 " ⊕ "  => Sum
scoped infixl:70 " & "  => Product
scoped infixl:25 " ⊢ "  => GrammarTerm
scoped notation "⊤g" => Top
scoped notation "⊥g" => Bottom
scoped notation "lit(" c ")" => Literal c
scoped notation "ε" => Epsilon
scoped syntax:50 "&[" ident " ∈ " term "]" term:50 : term
scoped syntax:50 "⊕[" ident " ∈ " term "]" term:50 : term

scoped macro_rules
  | `(&[$x:ident ∈ $X] $F) => `(IdxProduct $X (fun $x => $F))
scoped macro_rules
  | `(⊕[$x:ident ∈ $X] $F) => `(IdxCoproduct $X (fun $x => $F))

@[simp] theorem Literal.length_eq {c : Alphabet} {w : String Alphabet} (h : Literal c w) :
    w.length = 1 := by
  obtain ⟨⟨rfl⟩⟩ := h; rfl

@[simp] theorem Epsilon.length_eq {w : String Alphabet} (h : Epsilon w) :
    w.length = 0 := by
  obtain ⟨⟨rfl⟩⟩ := h; rfl

def elimTensor {A B : Grammar Alphabet} (C : String Alphabet → Sort _) {w : String Alphabet}
    (t : Tensor A B w) (body : (wL wR : String Alphabet) → A wL → B wR → C (wL ++ wR))
    : C w := t.split.eq ▸ body t.split.left t.split.right t.fst t.snd

/-- Like `elimTensor` but passes the splitting equality `wL ++ wR = w` into the body,
    so it remains visible for termination proofs. -/
def elimTensorH {A B : Grammar Alphabet} (C : String Alphabet → Sort _) {w : String Alphabet}
    (t : Tensor A B w)
    (body : (wL wR : String Alphabet) → A wL → B wR → (wL ++ wR = w) → C (wL ++ wR))
    : C w := t.split.eq ▸ body t.split.left t.split.right t.fst t.snd t.split.eq

def elimEpsilon (C : String Alphabet → Sort _) {w : String Alphabet}
    (t : Epsilon w) (body : C []) : C w := t.down.down ▸ body

end LambekD
