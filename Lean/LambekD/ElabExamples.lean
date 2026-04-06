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
  [| x => x |]

-- Tensor intro: A ⊗ B ⊢ A ⊗ B (identity on tensor, single pattern)
def tensorId (A B : Grammar) : A ⊗ B ⊢ A ⊗ B :=
  [| x => x |]

-- Tensor elimination + rebuild: A ⊗ B ⊢ A ⊗ B (multi-pattern)
def tensorLetId (A B : Grammar) : A ⊗ B ⊢ A ⊗ B :=
  [| a b => (a, b) |]

-- ═══════════════════════════════════════════════════════════
-- Linear function examples
-- ═══════════════════════════════════════════════════════════

-- Evaluation: A ⊗ (A ⊸ B) ⊢ B  (argument LEFT of function → right-app)
def evalR (A B : Grammar) : A ⊗ (A ⊸ B) ⊢ B :=
  [| a f => f a |]

-- Evaluation: (B ⟜ A) ⊗ A ⊢ B  (function LEFT of argument → left-app)
def evalL (A B : Grammar) : (B ⟜ A) ⊗ A ⊢ B :=
  [| f a => f a |]

-- ═══════════════════════════════════════════════════════════
-- Sum examples
-- ═══════════════════════════════════════════════════════════

-- Left injection: A ⊢ A ⊕ B
def injLeftEx (A B : Grammar) : A ⊢ A ⊕ B :=
  [| x => inl x |]

-- Right injection: B ⊢ A ⊕ B
def injRightEx (A B : Grammar) : B ⊢ A ⊕ B :=
  [| x => inr x |]

-- Case analysis: A ⊕ B ⊢ A ⊕ B (identity via case)
def caseId (A B : Grammar) : A ⊕ B ⊢ A ⊕ B :=
  [| x => case x of | inl a => inl a | inr b => inr b |]

-- ═══════════════════════════════════════════════════════════
-- Additive product examples
-- ═══════════════════════════════════════════════════════════

-- Pair: A ⊢ A & A (diagonal)
def diag (A : Grammar) : A ⊢ A & A :=
  [| x => ⟨x, x⟩ |]

-- First projection: A & B ⊢ A
def proj1 (A B : Grammar) : A & B ⊢ A :=
  [| x => fst x |]

-- Second projection: A & B ⊢ B
def proj2 (A B : Grammar) : A & B ⊢ B :=
  [| x => snd x |]

-- ═══════════════════════════════════════════════════════════
-- Non-examples (should fail)
-- ═══════════════════════════════════════════════════════════

set_option linter.unusedVariables false in
-- Contraction: A ⊢ A ⊗ A (uses variable twice — REJECTED)
example (A : Grammar) : True := by
  fail_if_success { have : A ⊢ A ⊗ A := [| x => (x, x) |] }
  trivial

set_option linter.unusedVariables false in
-- Exchange: A ⊗ B ⊢ B ⊗ A (reorders variables — REJECTED)
example (A B : Grammar) : True := by
  fail_if_success {
    have : A ⊗ B ⊢ B ⊗ A := [| a b => (b, a) |] }
  trivial

set_option linter.unusedVariables false in
-- Weakening: A ⊗ B ⊢ A (drops b — REJECTED)
example (A B : Grammar) : True := by
  fail_if_success {
    have : A ⊗ B ⊢ A := [| a b => a |] }
  trivial

set_option linter.unusedVariables false in
-- Wrong eval order: (A ⊸ B) ⊗ A ⊢ B (function LEFT of argument for ⊸ — REJECTED)
example (A B : Grammar) : True := by
  fail_if_success {
    have : (A ⊸ B) ⊗ A ⊢ B := [| f a => f a |] }
  trivial

-- ═══════════════════════════════════════════════════════════
-- Nested tensor examples
-- ═══════════════════════════════════════════════════════════

-- Reassociate: (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
def assocR (A B C : Grammar) : (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C) :=
  [| ab c => let (a, b) = ab in (a, (b, c)) |]

-- Reassociate the other way: A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
def assocL (A B C : Grammar) : A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C :=
  [| a bc => let (b, c) = bc in ((a, b), c) |]

-- Three-pattern reassociation
def assocR' (A B C : Grammar) : A ⊗ (B ⊗ C) ⊢ A ⊗ (B ⊗ C) :=
  [| a b c => (a, (b, c)) |]

-- ═══════════════════════════════════════════════════════════
-- Case + tensor mixed
-- ═══════════════════════════════════════════════════════════

-- Distribute: A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C)
def distribute (A B C : Grammar) : A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C) :=
  [| a bc =>
     case bc of
     | inl b => inl (a, b)
     | inr c => inr (a, c) |]

-- ═══════════════════════════════════════════════════════════
-- Lambda examples
-- ═══════════════════════════════════════════════════════════

-- Right curry: (A ⊗ B ⊸ C) ⊢ (B ⊸ (A ⊸ C))
def curryR (A B C : Grammar) : (A ⊗ B) ⊸ C ⊢ B ⊸ (A ⊸ C) :=
  [| g => fun (b : B) => fun (a : A) => g (a, b) |]

-- ═══════════════════════════════════════════════════════════
-- Escape hatch example
-- ═══════════════════════════════════════════════════════════

def myMorph (A : Grammar) : A ⊢ A := fun _ a => a

def escapedId (A : Grammar) : A ⊢ A :=
  [| x => #[myMorph A] x |]

-- Chain two morphisms
def escapedChain (A B C : Grammar) (f : A ⊢ B) (g : B ⊢ C) : A ⊢ C :=
  [| x => #[g] (#[f] x) |]

-- ═══════════════════════════════════════════════════════════
-- Nonlinear type dependence
-- ═══════════════════════════════════════════════════════════

def idParam (X : Type) (F : X → Grammar) (x : X) : F x ⊢ F x :=
  [| v => v |]

-- Tensor of dependent grammars
def tensorParam (X : Type) (F : X → Grammar) (x y : X) :
    F x ⊗ F y ⊢ F x ⊗ F y :=
  [| a b => (a, b) |]

-- Nonlinear control flow: the grammar depends on a Bool
def selectGrammar (A B : Grammar) (b : Bool) :
    (if b then A else B) ⊢ (if b then A else B) :=
  [| x => x |]

-- ═══════════════════════════════════════════════════════════
-- Indexed product / coproduct examples
-- ═══════════════════════════════════════════════════════════

-- Indexed product intro: A ⊢ &[x ∈ X] A  (constant family)
def idxProdConst (X : Type) (A : Grammar) : A ⊢ &[x ∈ X] A :=
  [| v => Λ (x : X) => v |]

-- Indexed product elim (projection): &[x ∈ Bool] F x ⊢ F true
def idxProdProj (F : Bool → Grammar) : &[x ∈ Bool] F x ⊢ F true :=
  [| v => v ⌈true⌉ |]

-- Indexed coproduct intro: F true ⊢ ⊕[x ∈ Bool] F x
def idxCoprodInj (F : Bool → Grammar) : F true ⊢ ⊕[x ∈ Bool] F x :=
  [| v => σ⟨true, v⟩ |]

-- Indexed coproduct elim: ⊕[x ∈ Bool] F x ⊢ ⊕[x ∈ Bool] F x
def idxCoprodCase (F : Bool → Grammar) : ⊕[x ∈ Bool] F x ⊢ ⊕[x ∈ Bool] F x :=
  [| v => caseDep v of | σ⟨x, y⟩ => σ⟨x, y⟩ |]

-- ═══════════════════════════════════════════════════════════
-- Sorry support
-- ═══════════════════════════════════════════════════════════

def sorryEx (A B : Grammar) : A ⊢ B := [| x => sorry |]
def sorryLet (A B C : Grammar) : A ⊗ B ⊢ C := [| a b => sorry |]

-- ═══════════════════════════════════════════════════════════
-- Product patterns
-- ═══════════════════════════════════════════════════════════

-- First projection via product pattern
def prodPatFst (A B : Grammar) : A & B ⊢ A := [| ⟨a, b⟩ => a |]

-- Second projection via product pattern
def prodPatSnd (A B : Grammar) : A & B ⊢ B := [| ⟨a, b⟩ => b |]

-- Product pattern identity
def prodPatId (A B : Grammar) : A & B ⊢ A & B := [| ⟨a, b⟩ => ⟨a, b⟩ |]

-- Product pattern with tensor
def prodTensor (A B C : Grammar) : (A & B) ⊗ C ⊢ A ⊗ C := [| ⟨a, b⟩ c => (a, c) |]

-- Product pattern contraction (should fail)
set_option linter.unusedVariables false in
example (A B : Grammar) : True := by
  fail_if_success { have : A & B ⊢ A ⊗ B := [| ⟨a, b⟩ => (a, b) |] }
  trivial

-- ═══════════════════════════════════════════════════════════
-- grammar_inductive examples
-- ═══════════════════════════════════════════════════════════

grammar_inductive StarG (A : Grammar) where
  | nil : Epsilon
  | cons : A ⊗ StarG A

def starNil (A : Grammar) : Epsilon ⊢ StarG A :=
  [| x => nil x |]

def starCons (A : Grammar) : A ⊗ StarG A ⊢ StarG A :=
  [| x => cons x |]

-- let-tensor + constructor
def starConsLet (A : Grammar) : A ⊗ StarG A ⊢ StarG A :=
  [| x => let (a, s) = x in cons (a, s) |]

-- rec: eliminate a StarG value
def starToSelf (A : Grammar) : StarG A ⊢ StarG A :=
  [| x => rec x of
     | nil y => nil y
     | cons y => cons y |]

-- ═══════════════════════════════════════════════════════════
-- Constructor auto-detect (sugar for `fold ctor arg`)
-- ═══════════════════════════════════════════════════════════

-- Using constructor name directly instead of `fold`
def starNil' (A : Grammar) : Epsilon ⊢ StarG A :=
  [| x => nil x |]

def starCons' (A : Grammar) : A ⊗ StarG A ⊢ StarG A :=
  [| x => cons x |]

-- ═══════════════════════════════════════════════════════════
-- Multi-tensor grammar_inductive (Dyck grammar)
-- ═══════════════════════════════════════════════════════════

grammar_inductive Dyck where
  | nil : Epsilon
  | cons : Literal Paren.lparen ⊗ Dyck ⊗ Literal Paren.rparen ⊗ Dyck

-- Constructor application without `fold` keyword
def dyckCons : Literal Paren.lparen ⊗ Dyck ⊗ Literal Paren.rparen ⊗ Dyck ⊢ Dyck :=
  [| x => cons x |]

-- Explicit `fold` still works
def dyckConsExplicit : Literal Paren.lparen ⊗ Dyck ⊗ Literal Paren.rparen ⊗ Dyck ⊢ Dyck :=
  [| x => fold cons x |]

-- Simple nil fold (to isolate rec issue)
def dyckNil : Epsilon ⊢ Dyck :=
  [| x => fold nil x |]

-- rec with multi-tensor constructor
def dyckToSelf : Dyck ⊢ Dyck :=
  [| x => rec x of
     | nil y => nil y
     | cons y => cons y |]

-- let-unit test
def letUnit (A : Grammar) : Epsilon ⊗ A ⊢ A :=
  [| x a => let ⟨⟩ = x in a |]

-- Nonempty instance needed for `partial` definitions
noncomputable instance (A B : Grammar) : Nonempty (A ⊢ B) := ⟨fun _ _ => sorry⟩

partial def append : Dyck ⊗ Dyck ⊢ Dyck :=
  [| d d' => rec d of
     -- some sort of nullary let for epsilon elimination
     | nil x => let () = x in d'
     -- multi arity pattern match
     | cons lp e rp e' =>
       -- multi arity constructors, function application,
       -- and can recurse using append
       cons lp e rp (append e' d')
   |]

end LambekD.ElabExamples
