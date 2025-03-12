{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.LiftFunctor (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX ℓY : Level

module _ (X : Type ℓX) {ℓY} where
  LiftFunctor : (F : Functor X) → Functor (Lift {j = ℓY} X)
  LiftFunctor (k A) = k (LiftG ℓY A)
  LiftFunctor (Var x) = Var (lift x)
  LiftFunctor (&e Y F) = &e (Lift {j = ℓY} Y) (λ y → LiftFunctor (F (lower y)))
  LiftFunctor (⊕e Y F) = ⊕e (Lift {j = ℓY} Y) (λ y → LiftFunctor (F (lower y)))
  LiftFunctor (F ⊗e F₁) = (LiftFunctor F) ⊗e (LiftFunctor F₁)

  lowerFunctor :
    {ℓB : Level} →
    (F : Functor X) → {A : X → Grammar ℓA}
    → ⟦ LiftFunctor F ⟧ (λ (lift x) → LiftG ℓB (A x)) ⊢ ⟦ F ⟧ A
  lowerFunctor (k A) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (Var x) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (&e Y F) = &ᴰ-intro (λ y → lowerFunctor (F y) ∘g π (lift y))
  lowerFunctor (⊕e Y F) = ⊕ᴰ-elim (λ (lift y) → σ y ∘g lowerFunctor (F y))
  lowerFunctor (F ⊗e F₁) = lowerFunctor F ,⊗ lowerFunctor F₁

  liftFunctor :
    {ℓB : Level} →
    (F : Functor X) → {A : X → Grammar ℓA}
    → ⟦ F ⟧ A ⊢ ⟦ LiftFunctor F ⟧ (λ (lift x) → LiftG ℓB (A x))
  liftFunctor (k A) = liftG ∘g liftG ∘g lowerG
  liftFunctor (Var x) = liftG ∘g liftG ∘g lowerG
  liftFunctor (&e Y F) = &ᴰ-intro (λ (lift y) → liftFunctor (F y) ∘g π y)
  liftFunctor (⊕e Y F) = ⊕ᴰ-elim (λ y → σ (lift y) ∘g liftFunctor (F y))
  liftFunctor (F ⊗e F₁) = liftFunctor F ,⊗ liftFunctor F₁

  open StrongEquivalence
  liftFunctor≅ :
    (F : Functor X) → {A : X → Grammar ℓA} →
    StrongEquivalence
    (⟦ LiftFunctor F ⟧ (λ (lift x) → LiftG ℓB (A x)))
    (⟦ F ⟧ A)
  liftFunctor≅ F .fun = lowerFunctor F
  liftFunctor≅ F .inv = liftFunctor F
  liftFunctor≅ (k A) .sec = refl
  liftFunctor≅ (Var X) .sec = refl
  liftFunctor≅ {ℓB = ℓB} (&e Y F) .sec =
    &ᴰ≡ _ _ (λ y → λ i →
      liftFunctor≅ {ℓB = ℓB} (F y) .sec i ∘g π y)
  liftFunctor≅ {ℓB = ℓB} (⊕e Y F) .sec =
    ⊕ᴰ≡ _ _ λ y → λ i → σ y ∘g liftFunctor≅ {ℓB = ℓB} (F y) .sec i
  liftFunctor≅ {ℓB = ℓB} (F ⊗e F₁) {A = A} .sec = ans
    where
      opaque
        unfolding ⊗-intro
        ans : lowerFunctor {ℓB = ℓB} F {A = A} ,⊗
                lowerFunctor {ℓB = ℓB} F₁ {A = A}
              ∘g liftFunctor F ,⊗ liftFunctor F₁ ≡ id
        ans i = liftFunctor≅ {ℓB = ℓB} F .sec i
          ,⊗ liftFunctor≅ {ℓB = ℓB} F₁ .sec i
  liftFunctor≅ (k A) .ret = refl
  liftFunctor≅ (Var x) .ret = refl
  liftFunctor≅ (&e Y F) .ret =
    &ᴰ≡ _ _ λ (lift y) → λ i →
      liftFunctor≅ (F y) .ret i ∘g π (lift y)
  liftFunctor≅ (⊕e Y F) .ret =
    ⊕ᴰ≡ _ _ λ (lift y) → λ i → σ (lift y) ∘g liftFunctor≅ (F y) .ret i
  liftFunctor≅ {ℓB = ℓB} (F ⊗e F₁) {A = A} .ret = ans
    where
      opaque
        unfolding ⊗-intro
        ans : liftFunctor {ℓB = ℓB} F {A = A} ,⊗
                 liftFunctor {ℓB = ℓB} F₁ {A = A}
              ∘g lowerFunctor F ,⊗ lowerFunctor F₁ ≡ id
        ans i = liftFunctor≅ {ℓB = ℓB} F .ret i ,⊗
          liftFunctor≅ {ℓB = ℓB} F₁ .ret i

  module _ {F : X → Functor X} where
    private
      X' = Lift {j = ℓY} X

      F' : X' → Functor X'
      F' (lift x) = LiftFunctor (F x)

    module _ {A : X → Grammar ℓA} where
      private
        L = ℓ-max ℓA (ℓ-max ℓX ℓY)

        g' : X' → Grammar L
        g' (lift x) = LiftG (ℓ-max ℓX ℓY) (A x)

      module _ (the-alg : Algebra F A) where
        LiftAlg : Algebra F' g'
        LiftAlg (lift x) = liftG ∘g the-alg x ∘g lowerFunctor (F x)
      module _ (the-alg : Algebra F' g') where
        LowerAlg : Algebra F A
        LowerAlg x = lowerG ∘g the-alg (lift x) ∘g liftFunctor (F x)
      module _ (the-alg : Algebra F' λ (lift x) → A x) where
        LowerAlg' : Algebra F A
        LowerAlg' x =
          the-alg (lift x)
          ∘g map (F' (lift x)) (λ _ → lowerG {ℓB = ℓA})
          ∘g liftFunctor (F x)

    module _ {x : X} where
      lowerF : μ F' (lift x) ⊢ μ F x
      lowerF =
        rec _
          (λ (lift y) →
            roll
            ∘g lowerFunctor {ℓB = ℓ-max ℓX ℓY} (F y)
            ∘g map (F' (lift y)) (λ _ → liftG))
          (lift x)

      liftF : μ F x ⊢ μ F' (lift x)
      liftF =
        rec _
          (λ y →
            roll
            ∘g map (F' (lift y)) (λ _ → lowerG)
            ∘g liftFunctor {ℓB = ℓ-max ℓX ℓY} (F y))
          x
