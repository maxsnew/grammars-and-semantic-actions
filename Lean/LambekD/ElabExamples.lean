import LambekD.Elab

/-!
# Elaborator examples and tests

Tests for the ordered linear DSL elaborator.
-/

namespace LambekD.ElabExamples

open LambekD LambekD.Elab

-- ═══════════════════════════════════════════════════════════
-- Alphabet for testing
-- ═══════════════════════════════════════════════════════════

inductive Paren where | lparen | rparen
  deriving Inhabited, DecidableEq

instance : AlphabetStr where
  Alphabet := Paren
  instInahbited := inferInstance
  instDecEq := inferInstance

-- ═══════════════════════════════════════════════════════════
-- Basic examples
-- ═══════════════════════════════════════════════════════════

-- Identity: A ⊢ A
def idMorph (A : Grammar) : A ⊢ A :=
  [| input |]

-- Tensor intro: A ⊗ B ⊢ A ⊗ B (identity on tensor)
def tensorId (A B : Grammar) : A ⊗ B ⊢ A ⊗ B :=
  [| input |]

-- Tensor elimination + rebuild: A ⊗ B ⊢ A ⊗ B
def tensorLetId (A B : Grammar) : A ⊗ B ⊢ A ⊗ B :=
  [| let (a, b) = input in (a, b) |]

-- ═══════════════════════════════════════════════════════════
-- Linear function examples
-- ═══════════════════════════════════════════════════════════

-- Right lambda identity: ⊢ A ⊸ A
-- The elaborator needs an empty context for this. Let's use the escape hatch.
-- Actually, [| ... |] always starts with one input variable. For closed terms
-- we'd need a different entry point. Let's test with open terms instead.

-- Evaluation: A ⊗ (A ⊸ B) ⊢ B  (argument LEFT of function → right-app)
def evalR (A B : Grammar) : A ⊗ (A ⊸ B) ⊢ B :=
  [| let (a, f) = input in f a |]

-- Evaluation: (B ⟜ A) ⊗ A ⊢ B  (function LEFT of argument → left-app)
def evalL (A B : Grammar) : (B ⟜ A) ⊗ A ⊢ B :=
  [| let (f, a) = input in f a |]

-- ═══════════════════════════════════════════════════════════
-- Sum examples
-- ═══════════════════════════════════════════════════════════

-- Left injection: A ⊢ A ⊕ B
def injLeftEx (A B : Grammar) : A ⊢ A ⊕ B :=
  [| inl input |]

-- Right injection: B ⊢ A ⊕ B
def injRightEx (A B : Grammar) : B ⊢ A ⊕ B :=
  [| inr input |]

-- Case analysis: A ⊕ B ⊢ A ⊕ B (identity via case)
def caseId (A B : Grammar) : A ⊕ B ⊢ A ⊕ B :=
  [| case input of | inl x => inl x | inr y => inr y |]

-- ═══════════════════════════════════════════════════════════
-- Additive product examples
-- ═══════════════════════════════════════════════════════════

-- Pair: A ⊢ A & A (diagonal)
def diag (A : Grammar) : A ⊢ A & A :=
  [| ⟨input, input⟩ |]

-- First projection: A & B ⊢ A
def proj1 (A B : Grammar) : A & B ⊢ A :=
  [| fst input |]

-- Second projection: A & B ⊢ B
def proj2 (A B : Grammar) : A & B ⊢ B :=
  [| snd input |]

-- ═══════════════════════════════════════════════════════════
-- Non-examples (should fail)
-- ═══════════════════════════════════════════════════════════

set_option linter.unusedVariables false in
-- Contraction: A ⊢ A ⊗ A (uses variable twice — REJECTED)
example (A : Grammar) : True := by
  fail_if_success { have : A ⊢ A ⊗ A := [| (input, input) |] }
  trivial

set_option linter.unusedVariables false in
-- Exchange: A ⊗ B ⊢ B ⊗ A (reorders variables — REJECTED)
example (A B : Grammar) : True := by
  fail_if_success {
    have : A ⊗ B ⊢ B ⊗ A := [| let (a, b) = input in (b, a) |] }
  trivial

set_option linter.unusedVariables false in
-- Weakening: A ⊗ B ⊢ A (drops b — REJECTED)
example (A B : Grammar) : True := by
  fail_if_success {
    have : A ⊗ B ⊢ A := [| let (a, b) = input in a |] }
  trivial

set_option linter.unusedVariables false in
-- Wrong eval order: (A ⊸ B) ⊗ A ⊢ B (function LEFT of argument for ⊸ — REJECTED)
example (A B : Grammar) : True := by
  fail_if_success {
    have : (A ⊸ B) ⊗ A ⊢ B := [| let (f, a) = input in f a |] }
  trivial

-- ═══════════════════════════════════════════════════════════
-- Nested tensor examples
-- ═══════════════════════════════════════════════════════════

-- Reassociate: (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
def assocR (A B C : Grammar) : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C) :=
  [| let (ab, c) = input in
     let (a, b) = ab in
     (a, (b, c)) |]

-- Reassociate the other way: A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
def assocL (A B C : Grammar) : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C :=
  [| let (a, bc) = input in
     let (b, c) = bc in
     ((a, b), c) |]

-- ═══════════════════════════════════════════════════════════
-- Case + tensor mixed
-- ═══════════════════════════════════════════════════════════

-- Distribute: A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C)
def distribute (A B C : Grammar) : A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C) :=
  [| let (a, bc) = input in
     case bc of
     | inl b => inl (a, b)
     | inr c => inr (a, c) |]

-- ═══════════════════════════════════════════════════════════
-- Lambda examples
-- ═══════════════════════════════════════════════════════════

-- Right curry: (A ⊗ B ⊸ C) ⊢ (B ⊸ (A ⊸ C))
def curryR (A B C : Grammar) : (A ⊗ B) ⊸ C ⊢ B ⊸ (A ⊸ C) :=
  [| fun (b : B) => fun (a : A) => input (a, b) |]

-- ═══════════════════════════════════════════════════════════
-- Escape hatch example
-- ═══════════════════════════════════════════════════════════

def myMorph (A : Grammar) : A ⊢ A := fun _ a => a

def escapedId (A : Grammar) : A ⊢ A :=
  [| #[myMorph A] input |]

-- Chain two morphisms
def escapedChain (A B C : Grammar) (f : A ⊢ B) (g : B ⊢ C) : A ⊢ C :=
  [| #[g] (#[f] input) |]

-- ═══════════════════════════════════════════════════════════
-- Nonlinear type dependence
-- ═══════════════════════════════════════════════════════════

-- The grammar can depend on a nonlinear parameter.
-- Here `F x` is a grammar that depends on an ordinary Lean value `x : X`.
-- The elaborator handles this because type annotations are elaborated by Lean.
def idParam (X : Type) (F : X → Grammar) (x : X) : F x ⊢ F x :=
  [| input |]

-- Tensor of dependent grammars
def tensorParam (X : Type) (F : X → Grammar) (x y : X) :
    F x ⊗ F y ⊢ F x ⊗ F y :=
  [| let (a, b) = input in (a, b) |]

-- Nonlinear control flow: the grammar depends on a Bool
def selectGrammar (A B : Grammar) (b : Bool) :
    (if b then A else B) ⊢ (if b then A else B) :=
  [| input |]

end LambekD.ElabExamples
