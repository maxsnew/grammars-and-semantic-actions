import LambekD.Elab
import LambekD.Tactic

/-!
# Elaborator examples and tests

Tests for the ordered linear DSL elaborator.
All signatures use `↑g(X ⊸ Y)` instead of `X ⊢ Y`.
-/

namespace LambekD.ElabExamples

open LambekD LambekD.Elab

-- ═══════════════════════════════════════════════════════════
-- Alphabet for testing
-- ═══════════════════════════════════════════════════════════

inductive Paren where | lparen | rparen
  deriving Inhabited, DecidableEq

-- ═══════════════════════════════════════════════════════════
-- Basic examples
-- ═══════════════════════════════════════════════════════════

-- Identity
def idMorph (A : Grammar Paren) : ↑g(A ⊸ A) :=
  [| x => x |]

-- Tensor intro (identity on tensor, single pattern)
def tensorId (A B : Grammar Paren) : ↑g(A ⊗ B ⊸ A ⊗ B) :=
  [| x => x |]

-- Tensor elimination + rebuild (multi-pattern)
def tensorLetId (A B : Grammar Paren) : ↑g(A ⊗ B ⊸ A ⊗ B) :=
  [| a b => (a, b) |]

-- ═══════════════════════════════════════════════════════════
-- Linear function examples
-- ═══════════════════════════════════════════════════════════

-- Evaluation: (A ⊸ B) ⊗ A ⊸ B  (function LEFT of argument → right-app)
def evalR (A B : Grammar Paren) : ↑g((A ⊸ B) ⊗ A ⊸ B) :=
  [| f a => f a |]

-- Evaluation: A ⊗ (B ⟜ A) ⊸ B  (argument LEFT of function → left-app)
def evalL (A B : Grammar Paren) : ↑g(A ⊗ (B ⟜ A) ⊸ B) :=
  [| a f => f a |]

-- ═══════════════════════════════════════════════════════════
-- Sum examples
-- ═══════════════════════════════════════════════════════════

-- Left injection
def injLeftEx (A B : Grammar Paren) : ↑g(A ⊸ (A ⊕ B)) :=
  [| x => inl x |]

-- Right injection
def injRightEx (A B : Grammar Paren) : ↑g(B ⊸ (A ⊕ B)) :=
  [| x => inr x |]

-- Case analysis (identity via case)
def caseId (A B : Grammar Paren) : ↑g((A ⊕ B) ⊸ (A ⊕ B)) :=
  [| x => case x of | inl a => inl a | inr b => inr b |]

-- ═══════════════════════════════════════════════════════════
-- Additive product examples
-- ═══════════════════════════════════════════════════════════

-- Pair (diagonal)
def diag (A : Grammar Paren) : ↑g(A ⊸ A & A) :=
  [| x => ⟨x, x⟩ |]

-- First projection
def proj1 (A B : Grammar Paren) : ↑g(A & B ⊸ A) :=
  [| x => fst x |]

-- Second projection
def proj2 (A B : Grammar Paren) : ↑g(A & B ⊸ B) :=
  [| x => snd x |]

-- ═══════════════════════════════════════════════════════════
-- Non-examples (should fail)
-- ═══════════════════════════════════════════════════════════

set_option linter.unusedVariables false in
-- Contraction: uses variable twice — REJECTED
example (A : Grammar Paren) : True := by
  fail_if_success { have : ↑g(A ⊸ A ⊗ A) := [| x => (x, x) |] }
  trivial

set_option linter.unusedVariables false in
-- Exchange: reorders variables — REJECTED
example (A B : Grammar Paren) : True := by
  fail_if_success {
    have : ↑g(A ⊗ B ⊸ B ⊗ A) := [| a b => (b, a) |] }
  trivial

set_option linter.unusedVariables false in
-- Weakening: drops b — REJECTED
example (A B : Grammar Paren) : True := by
  fail_if_success {
    have : ↑g(A ⊗ B ⊸ A) := [| a b => a |] }
  trivial

set_option linter.unusedVariables false in
-- Wrong eval order: A ⊗ (A ⊸ B) ⊸ B (argument LEFT of function for ⊸ — REJECTED)
example (A B : Grammar Paren) : True := by
  fail_if_success {
    have : ↑g(A ⊗ (A ⊸ B) ⊸ B) := [| a f => f a |] }
  trivial

-- ═══════════════════════════════════════════════════════════
-- Nested tensor examples
-- ═══════════════════════════════════════════════════════════

-- Reassociate: (A ⊗ B) ⊗ C ⊸ A ⊗ (B ⊗ C)
def assocR (A B C : Grammar Paren) : ↑g((A ⊗ B) ⊗ C ⊸ A ⊗ (B ⊗ C)) :=
  [| ab c => let (a, b) = ab in (a, (b, c)) |]

-- Reassociate the other way: A ⊗ (B ⊗ C) ⊸ (A ⊗ B) ⊗ C
def assocL (A B C : Grammar Paren) : ↑g(A ⊗ (B ⊗ C) ⊸ (A ⊗ B) ⊗ C) :=
  [| a bc => let (b, c) = bc in ((a, b), c) |]

-- Three-pattern reassociation
def assocR' (A B C : Grammar Paren) : ↑g(A ⊗ (B ⊗ C) ⊸ A ⊗ (B ⊗ C)) :=
  [| a b c => (a, (b, c)) |]

-- ═══════════════════════════════════════════════════════════
-- Case + tensor mixed
-- ═══════════════════════════════════════════════════════════

-- Distribute: A ⊗ (B ⊕ C) ⊸ (A ⊗ B) ⊕ (A ⊗ C)
def distribute (A B C : Grammar Paren) : ↑g(A ⊗ (B ⊕ C) ⊸ (A ⊗ B) ⊕ (A ⊗ C)) :=
  [| a bc =>
     case bc of
     | inl b => inl (a, b)
     | inr c => inr (a, c) |]

-- ═══════════════════════════════════════════════════════════
-- Lambda examples
-- ═══════════════════════════════════════════════════════════

-- Right curry: ((A ⊗ B) ⊸ C) ⊸ (A ⊸ (B ⊸ C))
def curryR (A B C : Grammar Paren) : ↑g(((A ⊗ B) ⊸ C) ⊸ (A ⊸ (B ⊸ C))) :=
  [| g => fun (a : A) => fun (b : B) => g (a, b) |]

-- ═══════════════════════════════════════════════════════════
-- Escape hatch example
-- ═══════════════════════════════════════════════════════════

def myMorph (A : Grammar Paren) : ↑g(A ⊸ A) := fun _ a => a

def escapedId (A : Grammar Paren) : ↑g(A ⊸ A) :=
  [| x => #[myMorph A] x |]

-- Chain two morphisms
def escapedChain (A B C : Grammar Paren) (f : A ⊢ B) (g : B ⊢ C) : ↑g(A ⊸ C) :=
  [| x => #[g] (#[f] x) |]

-- ═══════════════════════════════════════════════════════════
-- Nonlinear type dependence
-- ═══════════════════════════════════════════════════════════

def idParam (X : Type) (F : X → Grammar Paren) (x : X) : ↑g(F x ⊸ F x) :=
  [| v => v |]

-- Tensor of dependent grammars
def tensorParam (X : Type) (F : X → Grammar Paren) (x y : X) :
    ↑g(F x ⊗ F y ⊸ F x ⊗ F y) :=
  [| a b => (a, b) |]

-- Nonlinear control flow: the grammar depends on a Bool
def selectGrammar (A B : Grammar Paren) (b : Bool) :
    ↑g((if b then A else B) ⊸ (if b then A else B)) :=
  [| x => x |]

-- ═══════════════════════════════════════════════════════════
-- Indexed product / coproduct examples
-- ═══════════════════════════════════════════════════════════

-- Indexed product intro (constant family)
def idxProdConst (X : Type) (A : Grammar Paren) : ↑g(A ⊸ (&[x ∈ X] A)) :=
  [| v => Λ (x : X) => v |]

-- Indexed product elim (projection)
def idxProdProj (F : Bool → Grammar Paren) : ↑g((&[x ∈ Bool] F x) ⊸ F true) :=
  [| v => v ⌈true⌉ |]

-- Indexed coproduct intro
def idxCoprodInj (F : Bool → Grammar Paren) : ↑g(F true ⊸ (⊕[x ∈ Bool] F x)) :=
  [| v => σ⟨true, v⟩ |]

-- Indexed coproduct elim
def idxCoprodCase (F : Bool → Grammar Paren) : ↑g((⊕[x ∈ Bool] F x) ⊸ (⊕[x ∈ Bool] F x)) :=
  [| v => caseDep v of | σ⟨x, y⟩ => σ⟨x, y⟩ |]

-- ═══════════════════════════════════════════════════════════
-- Sorry support
-- ═══════════════════════════════════════════════════════════

def sorryEx (A B : Grammar Paren) : ↑g(A ⊸ B) := [| x => sorry |]
def sorryLet (A B C : Grammar Paren) : ↑g(A ⊗ B ⊸ C) := [| a b => sorry |]

-- ═══════════════════════════════════════════════════════════
-- Product patterns
-- ═══════════════════════════════════════════════════════════

-- First projection via product pattern
def prodPatFst (A B : Grammar Paren) : ↑g(A & B ⊸ A) := [| ⟨a, b⟩ => a |]

-- Second projection via product pattern
def prodPatSnd (A B : Grammar Paren) : ↑g(A & B ⊸ B) := [| ⟨a, b⟩ => b |]

-- Product pattern identity
def prodPatId (A B : Grammar Paren) : ↑g(A & B ⊸ A & B) := [| ⟨a, b⟩ => ⟨a, b⟩ |]

-- Product pattern with tensor
def prodTensor (A B C : Grammar Paren) : ↑g((A & B) ⊗ C ⊸ A ⊗ C) := [| ⟨a, b⟩ c => (a, c) |]

-- Product pattern contraction (should fail)
set_option linter.unusedVariables false in
example (A B : Grammar Paren) : True := by
  fail_if_success { have : ↑g(A & B ⊸ A ⊗ B) := [| ⟨a, b⟩ => (a, b) |] }
  trivial

-- ═══════════════════════════════════════════════════════════
-- grammar_inductive examples
-- ═══════════════════════════════════════════════════════════

grammar_inductive StarG (A : Grammar Paren) : Grammar Paren where
  | nil : GEpsilon
  | cons : A ⊗ StarG A

def starNil (A : Grammar Paren) : ↑g(GEpsilon ⊸ StarG A) :=
  [| x => nil x |]

def starCons (A : Grammar Paren) : ↑g(A ⊗ StarG A ⊸ StarG A) :=
  [| x => cons x |]

-- let-tensor + constructor
def starConsLet (A : Grammar Paren) : ↑g(A ⊗ StarG A ⊸ StarG A) :=
  [| x => let (a, s) = x in cons (a, s) |]

-- rec: eliminate a StarG value
def starToSelf (A : Grammar Paren) : ↑g(StarG A ⊸ StarG A) :=
  [| x => rec x of
     | nil y => nil y
     | cons y => cons y |]

-- ═══════════════════════════════════════════════════════════
-- Constructor auto-detect (sugar for `fold ctor arg`)
-- ═══════════════════════════════════════════════════════════

-- Using constructor name directly instead of `fold`
def starNil' (A : Grammar Paren) : ↑g(GEpsilon ⊸ StarG A) :=
  [| x => nil x |]

def starCons' (A : Grammar Paren) : ↑g(A ⊗ StarG A ⊸ StarG A) :=
  [| x => cons x |]

-- ═══════════════════════════════════════════════════════════
-- Multi-tensor grammar_inductive (Dyck grammar)
-- ═══════════════════════════════════════════════════════════

grammar_inductive Dyck : Grammar Paren where
  | nil : GEpsilon
  | cons : GLiteral Paren.lparen ⊗ Dyck ⊗ GLiteral Paren.rparen ⊗ Dyck

-- Constructor application without `fold` keyword
def dyckCons : ↑g(GLiteral Paren.lparen ⊗ Dyck ⊗ GLiteral Paren.rparen ⊗ Dyck ⊸ Dyck) :=
  [| x => cons x |]

-- Explicit `fold` still works
def dyckConsExplicit : ↑g(GLiteral Paren.lparen ⊗ Dyck ⊗ GLiteral Paren.rparen ⊗ Dyck ⊸ Dyck) :=
  [| x => fold cons x |]

-- Simple nil fold (to isolate rec issue)
def dyckNil : ↑g(GEpsilon ⊸ Dyck) :=
  [| x => fold nil x |]

-- rec with multi-tensor constructor
def dyckToSelf : ↑g(Dyck ⊸ Dyck) :=
  [| x => rec x of
     | nil y => nil y
     | cons y => cons y |]

-- let-unit test
def letUnit (A : Grammar Paren) : ↑g(GEpsilon ⊗ A ⊸ A) :=
  [| x a => let ⟨⟩ = x in a |]

-- ═══════════════════════════════════════════════════════════
-- Recursive case analysis via `case ... of` + self-reference
-- ═══════════════════════════════════════════════════════════

-- StarG map: structural recursion via direct sub-term (no `partial` needed)
def starMap (A B : Grammar Paren) (f : A ⊢ B) : ↑g(StarG A ⊸ StarG B) :=
  [| s => case s of
     | nil x => nil x
     | cons a s' => cons (#[f] a) (#[starMap A B f] s')
   |]

-- append: recursion on tensor component
def append : ↑g(Dyck ⊗ Dyck ⊸ Dyck) :=
  [| d d' => case d of
     | nil x => let () = x in d'
     | cons lp e rp e' => cons lp e rp (append e' d')
   |]
termination_by w _ => w.length
decreasing_by all_goals grammar_decreasing

-- ═══════════════════════════════════════════════════════════
-- Non-linear binder pattern matching (indexed grammar_inductive)
-- ═══════════════════════════════════════════════════════════

-- NL binder that is NOT an index: avoids Lean's parameter promotion.
-- n : Nat does not appear in the return type Counted w, so Lean cannot
-- promote it. Since n blocks the prefix, w also stays an index.
grammar_inductive Counted : Grammar Paren where
  | mk : ↑(&[ n ∈ Nat ] Counted)

-- casesOn with single NL binder
def countedCase : ↑g(Counted ⊸ Counted) :=
  [| t => case t of
     | mk n x => let () = x in mk n
  |]

-- rec with single NL binder
def countedRec : ↑g(Counted ⊸ Counted) :=
  [| t => rec t of
     | mk n x => let () = x in mk n
  |]

-- Two NL binders
grammar_inductive Counted2 : Grammar Paren where
  | mk : ↑(&[ n ∈ Nat ] &[ m ∈ Nat ] Counted2)

def counted2Case : ↑g(Counted2 ⊸ Counted2) :=
  [| t => case t of
     | mk n m x => let () = x in mk n m
  |]

end LambekD.ElabExamples
