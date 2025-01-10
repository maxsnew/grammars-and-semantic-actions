{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.LiftFunctor (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Helper
open import Grammar.Base Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term.Base Alphabet

private
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

module _ (A : Type ℓ) {ℓ'} where
  LiftFunctor : (F : Functor A) → Functor (Lift {j = ℓ'} A)
  LiftFunctor (k g) = k (LiftG ℓ' g)
  LiftFunctor (Var a) = Var (lift a)
  LiftFunctor (&e B F) = &e (Lift {j = ℓ'} B) (λ b → LiftFunctor (F (lower b)))
  LiftFunctor (⊕e B F) = ⊕e (Lift {j = ℓ'} B) (λ b → LiftFunctor (F (lower b)))
  LiftFunctor (⊗e F F₁) = ⊗e (LiftFunctor F) (LiftFunctor F₁)

  lowerFunctor :
    {ℓ''' : Level} →
    (F : Functor A) → {g : A → Grammar ℓ''}
    → ⟦ LiftFunctor F ⟧ (λ (lift a) → LiftG ℓ''' (g a)) ⊢ ⟦ F ⟧ g
  lowerFunctor (k g) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (Var a) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (&e B F) = &ᴰ-in (λ b → lowerFunctor (F b) ∘g &ᴰ-π (lift b))
  lowerFunctor (⊕e B F) = ⊕ᴰ-elim (λ (lift b) → ⊕ᴰ-in b ∘g lowerFunctor (F b))
  lowerFunctor (⊗e F F₁) = lowerFunctor F ,⊗ lowerFunctor F₁

  liftFunctor :
    {ℓ''' : Level} →
    (F : Functor A) → {g : A → Grammar ℓ''}
    → ⟦ F ⟧ g ⊢ ⟦ LiftFunctor F ⟧ (λ (lift a) → LiftG ℓ''' (g a))
  liftFunctor (k g) = liftG ∘g liftG ∘g lowerG
  liftFunctor (Var a) = liftG ∘g liftG ∘g lowerG
  liftFunctor (&e B F) = &ᴰ-in (λ (lift b) → liftFunctor (F b) ∘g &ᴰ-π b)
  liftFunctor (⊕e B F) = ⊕ᴰ-elim (λ b → ⊕ᴰ-in (lift b) ∘g liftFunctor (F b))
  liftFunctor (⊗e F F₁) = liftFunctor F ,⊗ liftFunctor F₁

  open StrongEquivalence
  liftFunctor≅ :
    (F : Functor A) → {g : A → Grammar ℓ''} →
    StrongEquivalence
    (⟦ LiftFunctor F ⟧ (λ (lift a) → LiftG ℓ''' (g a)))
    (⟦ F ⟧ g)
  liftFunctor≅ F .fun = lowerFunctor F
  liftFunctor≅ F .inv = liftFunctor F
  liftFunctor≅ (k g) .sec = refl
  liftFunctor≅ (Var a) .sec = refl
  liftFunctor≅ {ℓ''' = ℓ'''} (&e B F) .sec =
    &ᴰ≡ _ _ (λ b → λ i →
      liftFunctor≅ {ℓ''' = ℓ'''} (F b) .sec i ∘g &ᴰ-π b)
  liftFunctor≅ {ℓ''' = ℓ'''} (⊕e B F) .sec =
    ⊕ᴰ≡ _ _ λ b → λ i → ⊕ᴰ-in b ∘g liftFunctor≅ {ℓ''' = ℓ'''} (F b) .sec i
  liftFunctor≅ {ℓ''' = ℓ'''} (⊗e F F₁) {g = g} .sec = ans
    where
      opaque
        unfolding ⊗-intro
        ans : lowerFunctor {ℓ''' = ℓ'''} F {g = g} ,⊗
                lowerFunctor {ℓ''' = ℓ'''} F₁ {g = g}
              ∘g liftFunctor F ,⊗ liftFunctor F₁ ≡ id
        ans i = liftFunctor≅ {ℓ''' = ℓ'''} F .sec i
          ,⊗ liftFunctor≅ {ℓ''' = ℓ'''} F₁ .sec i
  liftFunctor≅ (k g) .ret = refl
  liftFunctor≅ (Var a) .ret = refl
  liftFunctor≅ (&e B F) .ret =
    &ᴰ≡ _ _ λ (lift b) → λ i →
      liftFunctor≅ (F b) .ret i ∘g &ᴰ-π (lift b)
  liftFunctor≅ (⊕e B F) .ret =
    ⊕ᴰ≡ _ _ λ (lift b) → λ i → ⊕ᴰ-in (lift b) ∘g liftFunctor≅ (F b) .ret i
  liftFunctor≅ {ℓ''' = ℓ'''} (⊗e F F₁) {g = g} .ret = ans
    where
      opaque
        unfolding ⊗-intro
        ans : liftFunctor {ℓ''' = ℓ'''} F {g = g} ,⊗
                 liftFunctor {ℓ''' = ℓ'''} F₁ {g = g}
              ∘g lowerFunctor F ,⊗ lowerFunctor F₁ ≡ id
        ans i = liftFunctor≅ {ℓ''' = ℓ'''} F .ret i ,⊗
          liftFunctor≅ {ℓ''' = ℓ'''} F₁ .ret i

  module _ {F : A → Functor A} where
    private
      A' = Lift {j = ℓ'} A

      F' : A' → Functor A'
      F' (lift a) = LiftFunctor (F a)

    module _ {g : A → Grammar ℓ''} where
      private
        L = ℓ-max ℓ'' (ℓ-max ℓ ℓ')

        g' : A' → Grammar L
        g' (lift a) = LiftG (ℓ-max ℓ ℓ') (g a)

      module _ (the-alg : Algebra F g) where
        LiftAlg : Algebra F' g'
        LiftAlg (lift a) = liftG ∘g the-alg a ∘g lowerFunctor (F a)
      module _ (the-alg : Algebra F' g') where
        LowerAlg : Algebra F g
        LowerAlg a = lowerG ∘g the-alg (lift a) ∘g liftFunctor (F a)
      module _ (the-alg : Algebra F' λ (lift a) → g a) where
        LowerAlg' : Algebra F g
        LowerAlg' a =
          the-alg (lift a)
          ∘g map (F' (lift a)) (λ _ → lowerG {ℓ' = ℓ''})
          ∘g liftFunctor (F a)

    module _ {a : A} where
      lowerF : μ F' (lift a) ⊢ μ F a
      lowerF =
        rec _
          (λ (lift a') →
            roll
            ∘g lowerFunctor {ℓ''' = ℓ-max ℓ ℓ'} (F a')
            ∘g map (F' (lift a')) (λ _ → liftG))
          (lift a)

      liftF : μ F a ⊢ μ F' (lift a)
      liftF =
        rec _
          (λ a' →
            roll
            ∘g map (F' (lift a')) (λ _ → lowerG)
            ∘g liftFunctor {ℓ''' = ℓ-max ℓ ℓ'} (F a'))
          a
