{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.RecursiveDescent.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.List.Properties
import Cubical.Data.Sum as Sum

open import Examples.Dyck
  hiding (LP ; RP)
  renaming ([ to LP ; ] to RP)

open import Grammar Alphabet hiding (Δ) renaming (NIL to *NIL)
open import Grammar.Maybe.Base Alphabet hiding (μ)
open import Grammar.Later.Base Alphabet
open import Grammar.Later.Properties Alphabet
open import Grammar.SemanticAction Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Parser.RecursiveDescent Alphabet
open import Term Alphabet

open StrongEquivalence

dyck-prefix-¬null : ⟨ ¬Nullable (literal LP ⊗ Dyck ⊗ literal RP) ⟩
dyck-prefix-¬null = ¬Nullable⊗l (disjoint-ε-literal LP)

fallback-nil : ∀  {ℓA} {A : Grammar ℓA} → A ⊢ MaybeLeft Dyck
fallback-nil = just ∘g NIL ,⊗ id ∘g ⊗-unit-l⁻ ∘g string-intro

-- just nil
nil-case : ▷ (MaybeLeft Dyck) & ε ⊢ MaybeLeft Dyck
nil-case =
  just
  ∘g id ,⊗ *NIL
  ∘g ⊗-unit-r⁻
  ∘g NIL
  ∘g π₂

-- Next character is RP, return just (NIL , rest-of-string)
rparen-branch : ▷ (MaybeLeft Dyck) & (literal RP ⊗ string) ⊢ MaybeLeft Dyck
rparen-branch =
  just
  ∘g NIL ,⊗ id
  ∘g ⊗-unit-l⁻
  ∘g string-intro
  ∘g π₂

tail-recurse :
  ▷ (MaybeLeft Dyck) & (literal LP ⊗ Dyck ⊗ literal RP ⊗ string) ⊢ MaybeLeft Dyck
tail-recurse =
  fmap (BALANCED ,⊗ id
        ∘g (id ,⊗ ⊗-assoc⁻) ,⊗ id
        ∘g ⊗-assoc⁻ ,⊗ id
        ∘g ⊗-assoc)
  ∘g Maybe⊗r
  ∘g ▷-app-NE dyck-prefix-¬null
  ∘g &-swap
  ∘g id ,&p reshape
  where
  reshape : literal LP ⊗ Dyck ⊗ literal RP ⊗ string ⊢ (literal LP ⊗ Dyck ⊗ literal RP) ⊗ ⊤
  reshape = id ,⊗ ⊤-intro ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc

post-inner-just : ▷ (MaybeLeft Dyck) & (literal LP ⊗ Dyck ⊗ string) ⊢ MaybeLeft Dyck
post-inner-just =
  ⊕-elim
    -- empty leftover after inner D: no RP to close, so the leading
    -- LP was not actually part of a balanced subterm
    fallback-nil
    (⊕ᴰ-elim leftover-char
     ∘g &⊕ᴰ-distR≅ .fun
     ∘g id ,&p ⊕ᴰ-distR .fun
     ∘g id ,&p (id ,⊗ ⊕ᴰ-distR .fun)
     ∘g id ,&p (id ,⊗ id ,⊗ ⊕ᴰ-distL .fun))
  ∘g &⊕-distL
  ∘g id ,&p ⊗⊕-distL
  ∘g id ,&p (id ,⊗ ⊗⊕-distL)
  ∘g id ,&p (id ,⊗ id ,⊗ unroll-string≅ .fun)
  where
  leftover-char : ∀ (c : Bracket) →
    ▷ (MaybeLeft Dyck) & (literal LP ⊗ Dyck ⊗ literal c ⊗ string) ⊢ MaybeLeft Dyck
  -- Same situation as above: the inner D ended but the next char isn't
  -- RP, so the leading LP couldn't be closed
  leftover-char LP = fallback-nil
  leftover-char RP = tail-recurse

lparen-branch : ▷ (MaybeLeft Dyck) & (literal LP ⊗ string) ⊢ MaybeLeft Dyck
lparen-branch =
  ⊕-elim
    post-inner-just
    -- Inner recursive call returned `nothing`.
    -- This is unreachable in practice as we can always fallback to nil
    fallback-nil
  ∘g &⊕-distL
  ∘g id ,&p Maybe⊗r
  ∘g id ,&p (⊗-unit-r ,⊗ id)
  ∘g id ,&p (id ,⊗ π₂)
  ∘g id ,&p ▷-app-NE-keep-⌈⌉ ((LP ∷ []) , ¬cons≡nil)
  ∘g id ,&p ((⊗-assoc ∘g id ,⊗ ⊗-unit-l⁻) ,&p id)
  ∘g π₁ ,& &-swap

first-char : ∀ (c : Bracket) →
  ▷ (MaybeLeft Dyck) & (literal c ⊗ string) ⊢ MaybeLeft Dyck
first-char LP = lparen-branch
first-char RP = rparen-branch

step' : ▷ (MaybeLeft Dyck) & string ⊢ MaybeLeft Dyck
step' =
  ⊕-elim
    nil-case
    (⊕ᴰ-elim first-char
     ∘g &⊕ᴰ-distR≅ .fun
     ∘g id ,&p ⊕ᴰ-distL .fun)
  ∘g &⊕-distL
  ∘g id ,&p unroll-string≅ .fun

step : ▷ (MaybeLeft Dyck) ⊢ MaybeLeft Dyck
step = step' ∘g id ,& string-intro

parseDyck : Parser Dyck
parseDyck = fixP step

recognizeDyck : string ⊢ Maybe Dyck
recognizeDyck = parse parseDyck

open import Examples.Benchmark.Dyck
open RunIncompleteParser (fmap abstractify ∘g recognizeDyck)

module partial =
  RunIncompleteParser (fmap (semact-concat abstractify semact-string) ∘g parseDyck)

opaque
  unfolding unfoldRecursiveDescentDefs genBALANCED eval-lex-uni

  -- Successes

  _ : parse? (fromString "")
  _ = Sum.inl (mt , tt) , refl

  _ : parse? (fromString "[]")
  _ = Sum.inl (bal mt mt , tt) , refl

  _ : parse? (fromString "[][]")
  _ = Sum.inl (bal mt (bal mt mt) , tt) , refl

  _ : parse? (fromString "[[]]")
  _ = Sum.inl (bal (bal mt mt) mt , tt) , refl

  -- Failures
  _ : parse? (fromString "[")
  _ = Sum.inr tt , refl

  _ : parse? (fromString "]")
  _ = Sum.inr tt , refl

  _ : parse? (fromString "[]]")
  _ = Sum.inr _ , refl

  -- Partial successes with nonempty leftover input

  _ : partial.parse? (fromString "]")
  _ = Sum.inl ((mt , RP ∷ []) , tt) , refl

  _ : partial.parse? (fromString "[]]")
  _ = Sum.inl ((bal mt mt , RP ∷ []) , tt) , refl

  _ : partial.parse? (fromString "[][")
  _ = Sum.inl ((bal mt mt , LP ∷ []) , tt) , refl

  _ : partial.parse? (fromString "[")
  _ = Sum.inl ((mt , LP ∷ []) , tt) , refl
