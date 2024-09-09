{- Grammar for one associative binary operation with constants and parens -}
module Examples.BinOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat as Nat
open import Cubical.Data.FinSet

data Tok : Type where
  LP RP : Tok   -- parens
  * : Tok       -- the binary operation
  num : ℕ → Tok -- constants

-- Alphabet : hSet _
-- Alphabet = Tok , {!!}

-- open import Grammar Alphabet
-- open import Grammar.KleeneStar Alphabet
-- open import Grammar.Equivalence Alphabet
-- open import Term Alphabet

-- anyNum : Grammar _
-- anyNum = LinΣ[ n ∈ ℕ ] literal (num n)
-- module LL⟨1⟩ where
--   Exp : Grammar ℓ-zero
--   data Atom : Grammar ℓ-zero

--   Exp = Atom ⊗ (KL* (literal * ⊗ Atom))
--   data Atom where
--     num : ∀ {n} iteral (num n) ⊢ Atom
--     parens : literal LP ⊗ Exp ⊗ literal RP ⊢ Atom
--   -- This grammar is LL(1) because after you match a close paren, you
--   -- need to look ahead one token to know if you continue matching
--   -- close parens or have finished parsing the Atom.
--   parens' = ⟜3-intro-ε parens

--   record Algebra ℓ : Type (ℓ-suc ℓ) where
--     field
--       UE : Grammar ℓ
--       UAs : Grammar ℓ
--       UA : Grammar ℓ

--       [mkExp] : UA ⊗ UAs ⊢ UE
--       [nil] : ε ⊢ UAs
--       [cons] : literal * ⊗ Atom ⊗ UAs ⊢ UAs
--       [num] : ∀ {n} → literal (num n) ⊢ UA
--       [parens] : literal LP ⊗ UE ⊗ literal RP ⊢ UA

-- module Automaton where
--   -- TODO: we should be able to generalize this definition to an
--   -- (infinite state) deterministic automaton with guarded
--   -- transitions.

--   -- the stack is a number,
--   -- the number of open parens that are closed by the term

--   -- Exp is for when we are parsing a single expression, Suffix is
--   -- when we are parsing the sequence of multiplications after an
--   -- expression

--   -- the boolean is whether it is an accepting or rejecting trace

--   -- three cases: Opening, Closing, Multiplying

--   -- Opening: at the start of an expression, the term starts with a
--   -- sequence of 0 or more opening parens, which we count. Ends when
--   -- we see a number, then we start closing
--   data Opening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   -- After we have seen a number we start closing parens until we
--   -- lookahead and see a *
--   data Closing : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   -- Parse a sequence of * Terms
--   data Multiplying : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero

--   data Opening where
--     left : ∀ {n b} → literal LP ⊗ Opening (suc n) b ⊢ Opening n b
--     num  : ∀ {n b} →
--       (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ Closing n b ⊢ Opening n b
--     unexpected : ∀ {n} → ε ⊕ (literal RP ⊕ literal *) ⊗ ⊤ ⊢ Opening n false

--   data Closing where
--     rightMore : ∀ {n b} →
--       literal RP ⊗ ((ε ⊕ literal RP ⊗ ⊤) & Closing n b) ⊢ Closing (suc n) b
--     rightDone : ∀ {n b} →
--       literal RP ⊗ ((literal * ⊗ ⊤) & Multiplying n b) ⊢ Closing (suc n) b
--     rightUnmatched : literal RP ⊗ ⊤ ⊢ Closing 0 false
--     rightUnexpectedLookahead : ∀ {n} →
--       literal RP ⊗ literal LP ⊗ ⊤ ⊢ Closing n false

--   data Multiplying where
--     times : ∀ {n b} → literal * ⊗ Opening n b ⊢ Multiplying n b
--     unexpected : ∀ {n} →
--       ε ⊕ (literal LP ⊕ literal RP ⊕ anyNum) ⊗ ⊤ ⊢ Multiplying n false

--   record Algebra ℓ : Type (ℓ-suc ℓ) where
--     field
--       UO : ℕ → Grammar ℓ
--       UC : ℕ → Grammar ℓ
--       UM : ℕ → Grammar ℓ
--       [left] : ∀ {n} → literal LP ⊗ UO (suc n) ⊢ UO n
--       [num]  : ∀ {n} → (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ UC n ⊢ UO n
--       [rightMore] : ∀ {n} →
--         literal RP ⊗ ((ε ⊕ literal RP ⊗ ⊤) & UC n) ⊢ UC (suc n)
--       [rightDone] : ∀ {n} →
  --       literal RP ⊗ ((literal * ⊗ ⊤) & UM n) ⊢ UC (suc n)
--       [times] : ∀ {n} → literal * ⊗ UO n ⊢ UM n

--   -- data Exp : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   -- data Suffix : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   -- data Exp where
--   --   invalid  : ∀ {n} → (ε ⊕ literal RP ⊕ literal *) ⊗ ⊤ ⊢ Exp n false
--   --   left     : ∀ {n b} →
--   --     literal LP ⊗ Exp (suc n) b ⊢
--   --       Exp n b -- this is wrong, need more states :/
--   --   num      : ∀ {n b} →
--   --     (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ Suffix n b ⊢ Exp n b
--   --   -- here is the lookahead part: to decide if we should keep parsing
--   --   -- the Exp or start parsing a Suffix, we need to check the next
--   --   -- character

--   --   -- if there are no more characters or the next character is a
--   --   -- close-paren, we continue parsing an Exp
--   --   rightMore : ∀ {n b} →
--   --     literal RP ⊗ ((ε ⊕ literal RP ⊗ ⊤) & Exp n b) ⊢ Exp (suc n) b
--   --   -- if the next character is a *, we start parsing a suffix
--   --   rightDone : ∀ {n b} →
--   --     literal RP ⊗ ((literal * ⊗ ⊤) & Suffix n b) ⊢ Exp (suc n) b
--   --   -- if the stack is 0, then this RP is unmatched, fail
--   --   rightUnmatch : literal RP ⊗ ⊤ ⊢ Exp 0 b
--   --   -- if the next character is an open paren, we fail
--   --   rightLookAhead : ∀ {n} →
--   --     (literal RP ⊕ ) ⊗ literal LP ⊗ ⊤ ⊢ Exp (suc n) false
--   -- data Suffix where
--   --   eofGood : ε ⊢ Suffix 0 true
--   --   eofBad : ∀ {n} → ε ⊢ Suffix (suc n) false

-- -- Soundness: i.e., that from every trace we can extract an LL(1) parse
-- module Soundness where
--   buildExp : Automaton.Opening 0 true ⊢ LL⟨1⟩.Exp
--   buildExp = {!!} where
--     open LL⟨1⟩ using (Exp; Atom)
--     open Automaton.Algebra
--     Stk : ℕ → Grammar ℓ-zero
--     Stk = Nat.elim ε-grammar
--       (λ _ Stk⟨n⟩ → literal RP ⊗ KL* (literal * ⊗ Atom) ⊗ Stk⟨n⟩)
--     alg : Automaton.Algebra ℓ-zero
--     alg .UO n = Exp ⊗ Stk n
--     alg .UC n = Stk n
--     alg .UM n = literal * ⊗ Atom ⊗ KL* (literal * ⊗ Atom) ⊗ Stk n
--     alg .[left] = ⊗-assoc ∘g ⟜3⊗ LL⟨1⟩.parens'
--     alg .[num] = LinΣ-elim (λ _ → Atom.num ,⊗ nil ∘g ⊗-unit-r⁻) ,⊗
--       id -- LinΣ-elim (λ _ → Atom.num) ,⊗ id
--     alg .[rightMore] =
--       id ,⊗ (⟜0⊗ nil ∘g &-π₂) -- nil ,⊗ id ,⊗ &-π₂ ∘g ⊗-unit-l⁻
--     alg .[rightDone] = id ,⊗ ((⟜2⊗ cons' ∘g ⊗-assoc ) ∘g &-π₂)
--     alg .[times] = id ,⊗ ⊗-assoc⁻
-- -- Completeness i.e., that every LL(1) parse has a trace. Though
-- -- completeness would be that every LL(1) parse corresponds to one we
-- -- extract from the previous function

-- -- kind of would want a truly dependent linear type here
-- -- to formulate it that way...
-- module Completeness where
--   mkTrace : LL⟨1⟩.Exp ⊢ Automaton.Opening 0 true
--   mkTrace = {!!} where
--     open LL⟨1⟩.Algebra
--     the-alg : LL⟨1⟩.Algebra ℓ-zero
--     the-alg .UE = {!!}
--     the-alg .UAs = {!!}
--     the-alg .UA = {!!}
--     the-alg .[mkExp] = {!!}
--     the-alg .[nil] = {!!}
--     the-alg .[cons] = {!!}
--     the-alg .[num] = {!!}
--     the-alg .[parens] = {!!}
