open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module @0 Grammar.LinearProduct.Conversion (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.AsEquality Alphabet
open import Grammar.Epsilon.AsPath Alphabet
  hiding (ε-intro)
  renaming (ε to εPath)
open import Grammar.Epsilon.Conversion Alphabet
open import Grammar.LinearProduct.AsEquality Alphabet
  hiding (⊗-unit-rr⁻)
open import Grammar.LinearProduct.AsPath Alphabet
  renaming (_⊗_ to _⊗Path_
          ; _,⊗_ to _,⊗Path_
          ; ⊗-intro to ⊗Path-intro
          ; ⊗-unit-r to ⊗Path-unit-r
          ; ⊗-unit-r⁻ to ⊗Path-unit-r⁻
          ; ⊗-unit-rr⁻ to ⊗Path-unit-rr⁻
          ; ⊗-unit-r⁻r to ⊗Path-unit-r⁻r
          ; ⊗≅ to ⊗Path≅)
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓF ℓG
      ℓH ℓK ℓL ℓM ℓN ℓO
      ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD
    E : Grammar ℓE
    F : Grammar ℓF
    G : Grammar ℓG
    H : Grammar ℓH
    K : Grammar ℓK
    L : Grammar ℓL
    M : Grammar ℓM
    N : Grammar ℓN
    O : Grammar ℓO
    f f' f'' f''' f'''' f''''' : A ⊢ B

opaque
  unfolding _⊗_ _⊗Path_
  ⊗→⊗Path : A ⊗ B ⊢ A ⊗Path B
  ⊗→⊗Path _ (s , a , b) = Splitting→SplittingPath _ s , a , b

  ⊗Path→⊗ : A ⊗Path B ⊢ A ⊗ B
  ⊗Path→⊗ _ (s , a , b) = SplittingPath→Splitting _ s , a , b

  ⊗Path→⊗→⊗Path : ⊗→⊗Path {A = A} {B = B} ∘g ⊗Path→⊗ ≡ id
  ⊗Path→⊗→⊗Path = funExt λ w → funExt λ where
    (s , a , b) → ΣPathP (SplittingIso w .Iso.rightInv s , refl)

  ⊗→⊗Path→⊗ : ⊗Path→⊗ {A = A} {B = B} ∘g ⊗→⊗Path ≡ id
  ⊗→⊗Path→⊗ = funExt λ w → funExt λ where
    (s , a , b) → ΣPathP (SplittingIso w .Iso.leftInv s , refl)

open StrongEquivalence

⊗≅⊗Path : A ⊗ B ≅ A ⊗Path B
⊗≅⊗Path .fun = ⊗→⊗Path
⊗≅⊗Path .inv = ⊗Path→⊗
⊗≅⊗Path .sec = ⊗Path→⊗→⊗Path
⊗≅⊗Path .ret = ⊗→⊗Path→⊗

⊗ε-eqToPath≅ : A ⊗ ε ≅ A ⊗Path εPath
⊗ε-eqToPath≅ =
  ⊗≅⊗Path
  ≅∙ ⊗Path≅ id≅ ε≅εPath

opaque
  unfolding _⊗_ ε εPath ⊗Path-unit-r ⊗-unit-r ⊗-intro ⊗Path-intro ⊗→⊗Path ε→εPath
  -- If equalities like this one can be proven as compatibilities
  -- between the AsPath and AsEquality variants of LinearProduct,
  -- then maybe we can use them as fixes to port old proofs over
  -- to the new definitons using Data.Equality
  ⊗-unit-r⁻≡ : ⊗-unit-r⁻ {A = A} ≡ ⊗ε-eqToPath≅ .inv ∘g ⊗Path-unit-r⁻
  ⊗-unit-r⁻≡ =
    funExt λ w → funExt λ where
     a →
      ΣPathP ((SplittingPathP refl) ,
              Σ≡Prop (λ _ → isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _))
                     refl)

  ⊗-unit-r≡ : ⊗-unit-r {A = A} ≡ ⊗Path-unit-r ∘g ⊗ε-eqToPath≅ .fun
  ⊗-unit-r≡ {A = A} =
    funExt λ w → funExt λ where
      (((w' , _) , Eq.refl) , a , Eq.refl) →
          (cong (λ z → Eq.transport A z a)
            (Eq.eqToPath (Eq.isPropPathToIsProp
              (isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _))
                _ (Eq.pathToEq (sym (++-unit-r w'))))))
          ∙ (Eq.eqToPath (Eq.transportPathToEq→transportPath A (sym (++-unit-r w')) a))
          ∙ (cong (λ z → subst A z a) (isSetString _ _ _ _))

⊗-unit-rr⁻ :
  ∀ {A : Grammar ℓA}
  → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
⊗-unit-rr⁻ {A = A} =
  (λ i → ⊗-unit-r⁻≡ i ∘g ⊗-unit-r≡ i) ∙
  (λ i → ⊗ε-eqToPath≅ .inv ∘g ⊗Path-unit-rr⁻ i ∘g ⊗ε-eqToPath≅ .fun) ∙
  ⊗ε-eqToPath≅ .ret
