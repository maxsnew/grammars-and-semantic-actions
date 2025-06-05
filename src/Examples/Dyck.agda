{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (_⊕_ ;_or_)
import Cubical.Data.Equality as Eq
import Cubical.Data.List as List
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Maybe hiding (rec)
open import Cubical.Data.Sum as Sum using (_⊎_ ; isSet⊎)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit

private
  variable
    ℓA ℓB ℓC : Level

data Bracket : Type where
  [ ] : Bracket

opaque
  BracketRep : Bracket ≃ Bool
  BracketRep = isoToEquiv (iso
    (λ { [ → true ; ] → false })
    (λ { false → ] ; true → [ })
    (λ { false → refl ; true → refl })
    λ { [ → refl ; ] → refl })

  isFinBracket : isFinSet Bracket
  isFinBracket = EquivPresIsFinSet (invEquiv BracketRep) isFinSetBool

  isSetBracket : isSet Bracket
  isSetBracket = isFinSet→isSet isFinBracket

LP = [
RP = ]

Alphabet : hSet _
Alphabet = (Bracket , isSetBracket)

open import Grammar Alphabet renaming (NIL to *NIL)
open import Grammar.Coherence Alphabet
open import Parser Alphabet
open import Term Alphabet

open StrongEquivalence

data DyckTag : Type ℓ-zero where
  nil' balanced' : DyckTag

isSetDyckTag : isSet DyckTag
isSetDyckTag = isSetRetract enc dec retr isSetBool where
  enc : DyckTag → Bool
  enc nil' = false
  enc balanced' = true
  dec : Bool → DyckTag
  dec false = nil'
  dec true = balanced'
  retr : (x : DyckTag) → dec (enc x) ≡ x
  retr nil' = refl
  retr balanced' = refl

DyckTy : Unit → Functor Unit
DyckTy _ = ⊕e DyckTag (λ
  { nil' → k ε
  ; balanced' → (k (literal [)) ⊗e (Var _) ⊗e (k (literal ]) ⊗e (Var _)) })

Dyck : Grammar ℓ-zero
Dyck = μ DyckTy _

isSetGrammarDyck : isSetGrammar Dyck
isSetGrammarDyck = isSetGrammarμ DyckTy
  (λ _ → isSetDyckTag ,
    (λ { nil' → isSetGrammarε
       ; balanced' → isSetGrammarLiteral _ , (tt* , (isSetGrammarLiteral _ , tt*)) }))
  tt

NIL : ε ⊢ Dyck
NIL = roll ∘g σ nil' ∘g liftG

BALANCED : literal [ ⊗ Dyck ⊗ literal ] ⊗ Dyck ⊢ Dyck
BALANCED = roll ∘g σ balanced' ∘g liftG ,⊗ liftG ,⊗ liftG ,⊗ liftG

GenDyck : ℕ → Grammar _
GenDyck 0         = Dyck
GenDyck (suc n-1) = Dyck ⊗ literal RP ⊗ GenDyck n-1

opaque
  genBALANCED : ∀ n → literal LP ⊗ Dyck ⊗ literal RP ⊗ GenDyck n ⊢ GenDyck n
  genBALANCED zero   = BALANCED
  genBALANCED (suc n) = BALANCED ,⊗ id ∘g ⊗-assoc4

¬GD : Grammar ℓ-zero
¬GD = (⊕ᴰ GenDyck ⇒ ⊥) ⟜ ⊤

lem : ＂ [ ＂ ⊗ Dyck ⊢ ¬GD
lem = ⟜-intro {!!}

lem' : char ⊗ ¬GD ⊢ ¬GD
lem' = ⟜-intro ((⟜-app ∘g ⊤-intro ,⊗ id) ∘g ⊗-assoc)

disjGD : disjoint (⊕ᴰ GenDyck) ¬GD
disjGD =
  disjoint⊢ ⇒-app (⟜-app ∘g ⊤-intro ,⊗ id ∘g ⊗-unit-l⁻)
  ∘g &-swap

disjGD' : disjoint Dyck ¬GD
disjGD' = disjoint⊢ disjGD (σ 0)

-- Should be true but not sure if there is a
-- quick way to show it
-- Maybe this follows from the totality of the
-- "completeParser" below
disjointSummandsGD : disjointSummands⊕ᴰ GenDyck
disjointSummandsGD = {!!}

-- Follows from disjointSummandsGD
disjointDyckGDSuc : disjoint Dyck (⊕[ n ∈ ℕ ] GenDyck (suc n))
disjointDyckGDSuc = {!!}

-- This weak parser is finished, even ignoring the open holes in this file
weakGDParser : weakParser (⊕ᴰ GenDyck)
weakGDParser =
  fold*r char
  (inl ∘g σ 0 ∘g NIL)
  (⊕-elim
    ((⊕ᴰ-elim λ where
      0 → ⊕ᴰ-elim (λ where
        [ → inr ∘g ⊤-intro
        ] → inl ∘g σ 1 ∘g NIL ,⊗ id ∘g ⊗-unit-l⁻)
      (suc n) → ⊕ᴰ-elim λ where
        [ → inl ∘g σ n ∘g genBALANCED n
        ] → inl ∘g σ (suc (suc n)) ∘g NIL ,⊗ id ∘g ⊗-unit-l⁻)
    ∘g map⊕ᴰ (λ n → ⊕ᴰ-distL .fun)
    ∘g ⊕ᴰ-distR .fun)
    (inr ∘g ⊤-intro)
    ∘g ⊗⊕-distL)


-- Same thing but with a richer complement type
completeParser : string ⊢ ⊕ᴰ GenDyck ⊕ ¬GD
completeParser =
  fold*r char
  (inl ∘g σ 0 ∘g NIL)
  (⊕-elim
    ((⊕ᴰ-elim λ where
      0 → ⊕ᴰ-elim (λ where
        [ → inr ∘g lem
        ] → inl ∘g σ 1 ∘g NIL ,⊗ id ∘g ⊗-unit-l⁻)
      (suc n) → ⊕ᴰ-elim λ where
        [ → inl ∘g σ n ∘g genBALANCED n
        ] → inl ∘g σ (suc (suc n)) ∘g NIL ,⊗ id ∘g ⊗-unit-l⁻)
    ∘g map⊕ᴰ (λ n → ⊕ᴰ-distL .fun)
    ∘g ⊕ᴰ-distR .fun)
    (inr ∘g lem')
    ∘g ⊗⊕-distL)

open Parser

-- TODO put this somewhere
disjoint⊕ : ∀ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} →
  disjoint A B → disjoint A C → disjoint A (B ⊕ C)
disjoint⊕ dis dis' =
  ⊕-elim dis dis'
  ∘g &⊕-distL

GDParser : Parser (⊕ᴰ GenDyck) ¬GD
GDParser .disj = disjGD
GDParser .fun = completeParser

DyckParser : Parser Dyck (¬GD ⊕ (⊕[ n ∈ ℕ ] GenDyck (suc n)))
DyckParser .disj = disjoint⊕ disjGD' disjointDyckGDSuc
DyckParser .fun =
  ⊕-elim
    (⊕ᴰ-elim λ where
       0 → inl
       (suc n) → inr ∘g inr ∘g σ n
    )
    (inr ∘g inl)
  ∘g GDParser .fun

weakDyckParser : weakParser Dyck
weakDyckParser =
  ⊕-elim
    (⊕ᴰ-elim λ where
       0 → inl
       (suc n) → inr ∘g ⊤-intro
    )
    inr
  ∘g weakGDParser

-- ⟜
open StrongEquivalence
deriv? : GenDyck 1 ≅ (Dyck ⟜ ＂ LP ＂)
deriv? .fun = ⟜-intro BALANCED
-- This map is definable with the right adjoint to the derivative
deriv? .inv = {!!}
deriv? .sec = {!!}
deriv? .ret = {!!}

-- I suspect these also hold
push : ∀ n → GenDyck (suc n) ≅ (GenDyck n ⟜ ＂ LP ＂)
push = {!!}

pop : ∀ n → GenDyck n ≅ (GenDyck (suc n) ⟜ ＂ RP ＂)
pop = {!!}

-- TODO overload string literals to make writing this easier
s : String
s =
  LP List.∷ LP List.∷
  LP List.∷ RP List.∷
  LP List.∷ RP List.∷
  RP List.∷ RP List.∷ List.[]

-- Sample input
opaque
  unfolding ⊗-intro ⊕ᴰ-distR ⊕ᴰ-distL ⊕-elim weakParserAccept? ⊗⊕-distL
  _ : weakParserAccept? weakDyckParser s ≡ true -- balanced
  _ = refl

  _ : weakParserAccept? weakDyckParser (RP List.∷ s) ≡ false -- unbalanceed
  _ = refl

  _ : weakParserAccept? weakDyckParser (LP List.∷ s) ≡ false
  _ = refl

  _ : weakParserAccept? weakDyckParser (LP List.∷ RP List.∷ s) ≡ true
  _ = refl

-- To define the Dyck Parser, above we defined a more general GenDyck parser.
-- Abstracting over this observation on derivatives, it then seems we are building a parser
-- for a family of grammars isomorphic to derivatives of the target grammar
--
-- Because these derivatives can be thought of as the states in a deterministic automaton,
-- we are implicitly constructing this automaton but never have to materialize the
-- DeterministicAutomaton
--
-- TODO how do we abstract over this observation?
-- TODO Figure out if this is this the exact same usage of derivatives as
-- Might's "Parsing with Derivatives"
