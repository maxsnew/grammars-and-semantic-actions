import LambekD.Core.Base

/-!
# Linear type connectives for Lambek^D

All grammar connectives, notation, and eliminators.
No metaprogramming dependencies.
-/

namespace LambekD

universe uAlph

variable {Alphabet : Type uAlph}

structure GTensor
  (A B : Grammar Alphabet)
  (w : String Alphabet) where
  split : Splitting w
  fst : A split.left
  snd : B split.right

def GEpsilon.{u} : Grammar.{u} Alphabet := fun w => ULift.{u} (PLift (w = []))
def GLiteral.{u} (c : Alphabet) : Grammar.{u} Alphabet := fun w => ULift.{u} (PLift (w = [c]))
def GFunctionR (A B : Grammar Alphabet) : Grammar Alphabet := fun w => ∀ w', A w' → B (w ++ w')
def GFunctionL (B A : Grammar Alphabet)
  : Grammar Alphabet := fun w => ∀ w', A w' → B (w' ++ w)
def GSum (A : Grammar Alphabet) (B : Grammar Alphabet)
  : Grammar Alphabet := fun w => A w ⊕ B w
def GProduct (A : Grammar Alphabet) (B : Grammar Alphabet)
  : Grammar Alphabet := fun w => A w × B w
def GTop.{u} : Grammar.{u} Alphabet := fun _ => ULift.{u} PUnit
def GBottom.{u} : Grammar.{u} Alphabet := fun _ => ULift.{u} PEmpty
def GIdxProduct.{v} (X : Type v) (F : X → Grammar Alphabet) : Grammar Alphabet := fun w => ∀ x, F x w
def GIdxCoproduct.{v} (X : Type v) (F : X → Grammar Alphabet) : Grammar Alphabet := fun w => Σ x, F x w

def GrammarTerm (A B : Grammar Alphabet) := ∀ w, A w → B w

/-- Parses of grammar A at the empty string. `↑g(A ⊸ B) ≅ A ⊢ B`. -/
def Element (A : Grammar Alphabet) := A []

scoped infixr:70 " ⊗ "  => GTensor
scoped infixr:60 " ⊸ "  => GFunctionR
scoped infixl:60 " ⟜ "  => GFunctionL
scoped infixl:65 " ⊕ "  => GSum
scoped infixl:70 " & "  => GProduct
scoped infixl:25 " ⊢ "  => GrammarTerm
scoped prefix:max "↑g" => Element
scoped notation "⊤g" => GTop
scoped notation "⊥g" => GBottom
scoped notation "lit(" c ")" => GLiteral c
scoped notation "ε" => GEpsilon
scoped syntax:50 "&[" ident " ∈ " term "]" term:50 : term
scoped syntax:50 "⊕[" ident " ∈ " term "]" term:50 : term

scoped macro_rules
  | `(&[$x:ident ∈ $X] $F) => `(GIdxProduct $X (fun $x => $F))
scoped macro_rules
  | `(⊕[$x:ident ∈ $X] $F) => `(GIdxCoproduct $X (fun $x => $F))

@[simp] theorem GLiteral.length_eq {c : Alphabet} {w : String Alphabet} (h : GLiteral c w) :
    w.length = 1 := by
  obtain ⟨⟨rfl⟩⟩ := h; rfl

@[simp] theorem GEpsilon.length_eq {w : String Alphabet} (h : GEpsilon w) :
    w.length = 0 := by
  obtain ⟨⟨rfl⟩⟩ := h; rfl

def gelimTensor {A B : Grammar Alphabet} (C : String Alphabet → Sort _) {w : String Alphabet}
    (t : GTensor A B w) (body : (wL wR : String Alphabet) → A wL → B wR → C (wL ++ wR))
    : C w := t.split.eq ▸ body t.split.left t.split.right t.fst t.snd

def gelimEpsilon (C : String Alphabet → Sort _) {w : String Alphabet}
    (t : GEpsilon w) (body : C []) : C w := t.down.down ▸ body

end LambekD
