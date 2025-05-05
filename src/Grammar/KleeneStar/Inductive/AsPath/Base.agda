{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module @0 Grammar.KleeneStar.Inductive.AsPath.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet isSetAlphabet
-- open import Grammar.Properties Alphabet isSetAlphabet
open import Grammar.Sum.Base Alphabet isSetAlphabet
-- open import Grammar.Sum.Properties Alphabet isSetAlphabet
open import Grammar.Epsilon.AsPath.Base Alphabet isSetAlphabet
open import Grammar.LinearProduct.AsPath.Base Alphabet isSetAlphabet
open import Grammar.LinearFunction.AsPath Alphabet isSetAlphabet
-- open import Grammar.Equivalence.Base Alphabet isSetAlphabet
-- open import Grammar.Equalizer.Base Alphabet isSetAlphabet
open import Grammar.Lift.Base Alphabet isSetAlphabet
open import Grammar.Inductive.AsPath.Indexed Alphabet isSetAlphabet
-- open import Grammar.Inductive.Properties Alphabet isSetAlphabet
open import Term.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

module _ (A : Grammar ℓA) where
  data *Tag : Type ℓA where
    nil cons : *Tag

  *Ty : Unit* {ℓA} → Functor Unit*
  *Ty _ = ⊕e *Tag (λ { nil → k ε* ; cons → (k A) ⊗e (Var _)})

  isFinSet*Tag : isFinSet *Tag
  isFinSet*Tag =
    EquivPresIsFinSet
      (isoToEquiv (iso
        (λ { (inl tt) → nil ; (inr (inl tt)) → cons})
        (λ { nil → inl tt ; cons → inr (inl tt)})
        (λ { nil → refl ; cons → refl})
        λ { (inl tt) → refl ; (inr (inl tt)) → refl}
        ))
      (isFinSetFin {n = 2})

  KL* : Grammar ℓA
  KL* = μ *Ty _

  fold*r' : Algebra *Ty (λ _ → B) → KL* ⊢ B
  fold*r' alg = rec *Ty alg _

  fold*r : (ε ⊢ B) → A ⊗ B ⊢ B → KL* ⊢ B
  fold*r [nil] [cons] = fold*r' (λ _ → ⊕ᴰ-elim λ where
    nil  → [nil] ∘g lowerG ∘g lowerG
    cons → [cons] ∘g lowerG ,⊗ lowerG)

  data *TagL : Type ℓA where
    nil snoc : *TagL

  *LTy : Unit* {ℓA} → Functor Unit*
  *LTy _ = ⊕e *TagL (λ { nil → k ε* ; snoc → (Var _) ⊗e (k A)})

  *LAlg→*Alg : Algebra *LTy (λ _ → B)  → Algebra *Ty (λ _ → B ⟜ B)
  *LAlg→*Alg l-alg _ = ⊕ᴰ-elim (λ {
      nil → ⟜-intro-ε id ∘g lowerG ∘g lowerG
    ; cons →
      ⟜-intro (
        ⟜-app
        ∘g (l-alg _ ∘g σ snoc ∘g liftG ,⊗ liftG) ,⊗ id
        ∘g ⊗-assoc) ∘g lowerG ,⊗ lowerG
        })

  fold*l' : Algebra *LTy (λ _ → B) → KL* ⊢ B
  fold*l' alg = ⟜-app ∘g (alg _ ∘g σ nil ∘g liftG ∘g liftG) ,⊗ fold*r' (*LAlg→*Alg alg) ∘g ⊗-unit-l⁻

  fold*l : (ε ⊢ B) → B ⊗ A ⊢ B → KL* ⊢ B
  fold*l [nil] [snoc] = fold*l' (λ _ → ⊕ᴰ-elim λ where
    nil  → [nil] ∘g lowerG ∘g lowerG
    snoc → [snoc] ∘g lowerG ,⊗ lowerG)

  *L : Grammar ℓA
  *L = μ *LTy _

_* : Grammar ℓA → Grammar ℓA
A * = KL* A
infix 40 _*

_+ : Grammar ℓA → Grammar ℓA
A + = A ⊗ A *
infix 40 _+

_+L : Grammar ℓA → Grammar ℓA
A +L = A * ⊗ A
infix 40 _+L

NIL : ∀ {A : Grammar ℓA} → ε ⊢ A *
NIL = roll ∘g σ nil ∘g liftG ∘g liftG

NIL-L : ∀ {A : Grammar ℓA} → ε ⊢ *L A
NIL-L = roll ∘g σ nil ∘g liftG ∘g liftG

CONS : ∀ {A : Grammar ℓA} → A ⊗ A * ⊢ A *
CONS = roll ∘g σ cons ∘g liftG ,⊗ liftG

SNOC : ∀ {A : Grammar ℓA} → *L A ⊗ A ⊢ *L A
SNOC = roll ∘g σ snoc ∘g liftG ,⊗ liftG

+→* : (A : Grammar ℓA) → A + ⊢ A *
+→* A = CONS

+-singleton : (A : Grammar ℓA) → A ⊢ A +
+-singleton A = id ,⊗ NIL ∘g ⊗-unit-r⁻

+L-singleton : (A : Grammar ℓA) → A ⊢ A +L
+L-singleton A = NIL ,⊗ id ∘g ⊗-unit-l⁻

+-cons : (A : Grammar ℓA) → A ⊗ A + ⊢ A +
+-cons A = id ,⊗ +→* A

*-singleton : (A : Grammar ℓA) → A ⊢ A *
*-singleton A = CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻
